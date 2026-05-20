import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [100,110). -/

/-- Block 100 covers tail-support indices [7500,7525) and q from 12389 to 12430. -/

def TailChunk000Sub001Block100Part000SupportExplicit : Finset ℕ :=
  ([12389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part000 : ℚ :=
  (286746290125 : ℚ) / 42589215130963673088

def SurrogateDiagonalTailChunk000Sub001Block100Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12389
    = surrogateDiagTailX0RatChunk000Sub001Block100Part000

theorem surrogateDiagonalTailChunk000Sub001Block100Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part000] using hcert

def TailChunk000Sub001Block100Part001SupportExplicit : Finset ℕ :=
  ([12390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part001 : ℚ :=
  (889976947675 : ℚ) / 150211707410055168

def SurrogateDiagonalTailChunk000Sub001Block100Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12390
    = surrogateDiagTailX0RatChunk000Sub001Block100Part001

theorem surrogateDiagonalTailChunk000Sub001Block100Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part001] using hcert

def TailChunk000Sub001Block100Part002SupportExplicit : Finset ℕ :=
  ([12391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block100Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12391
    = surrogateDiagTailX0RatChunk000Sub001Block100Part002

theorem surrogateDiagonalTailChunk000Sub001Block100Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part002] using hcert

def TailChunk000Sub001Block100Part003SupportExplicit : Finset ℕ :=
  ([12394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part003 : ℚ :=
  (600043890625 : ℚ) / 921324253413241632

def SurrogateDiagonalTailChunk000Sub001Block100Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12394
    = surrogateDiagTailX0RatChunk000Sub001Block100Part003

theorem surrogateDiagonalTailChunk000Sub001Block100Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part003] using hcert

def TailChunk000Sub001Block100Part004SupportExplicit : Finset ℕ :=
  ([12395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part004 : ℚ :=
  (75585333125 : ℚ) / 1854641119151259648

def SurrogateDiagonalTailChunk000Sub001Block100Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12395
    = surrogateDiagTailX0RatChunk000Sub001Block100Part004

theorem surrogateDiagonalTailChunk000Sub001Block100Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part004] using hcert

def TailChunk000Sub001Block100Part005SupportExplicit : Finset ℕ :=
  ([12398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part005 : ℚ :=
  (600431265625 : ℚ) / 922514402463305202

def SurrogateDiagonalTailChunk000Sub001Block100Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12398
    = surrogateDiagTailX0RatChunk000Sub001Block100Part005

theorem surrogateDiagonalTailChunk000Sub001Block100Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part005] using hcert

def TailChunk000Sub001Block100Part006SupportExplicit : Finset ℕ :=
  ([12399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part006 : ℚ :=
  (1067187938075 : ℚ) / 5831202148903855104

def SurrogateDiagonalTailChunk000Sub001Block100Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12399
    = surrogateDiagTailX0RatChunk000Sub001Block100Part006

theorem surrogateDiagonalTailChunk000Sub001Block100Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part006] using hcert

def TailChunk000Sub001Block100Part007SupportExplicit : Finset ℕ :=
  ([12401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block100Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12401
    = surrogateDiagTailX0RatChunk000Sub001Block100Part007

theorem surrogateDiagonalTailChunk000Sub001Block100Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part007] using hcert

def TailChunk000Sub001Block100Part008SupportExplicit : Finset ℕ :=
  ([12403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part008 : ℚ :=
  (72636461875 : ℚ) / 54815535742290905088

def SurrogateDiagonalTailChunk000Sub001Block100Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12403
    = surrogateDiagTailX0RatChunk000Sub001Block100Part008

theorem surrogateDiagonalTailChunk000Sub001Block100Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part008] using hcert

def TailChunk000Sub001Block100Part009SupportExplicit : Finset ℕ :=
  ([12405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part009 : ℚ :=
  (224122231175 : ℚ) / 595959859563565056

def SurrogateDiagonalTailChunk000Sub001Block100Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12405
    = surrogateDiagTailX0RatChunk000Sub001Block100Part009

theorem surrogateDiagonalTailChunk000Sub001Block100Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part009] using hcert

def TailChunk000Sub001Block100Part010SupportExplicit : Finset ℕ :=
  ([12406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part010 : ℚ :=
  (601206390625 : ℚ) / 924898159367354802

def SurrogateDiagonalTailChunk000Sub001Block100Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12406
    = surrogateDiagTailX0RatChunk000Sub001Block100Part010

theorem surrogateDiagonalTailChunk000Sub001Block100Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part010] using hcert

def TailChunk000Sub001Block100Part011SupportExplicit : Finset ℕ :=
  ([12407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part011 : ℚ :=
  (72625468225 : ℚ) / 15811970940019316736

def SurrogateDiagonalTailChunk000Sub001Block100Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12407
    = surrogateDiagTailX0RatChunk000Sub001Block100Part011

theorem surrogateDiagonalTailChunk000Sub001Block100Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part011] using hcert

def TailChunk000Sub001Block100Part012SupportExplicit : Finset ℕ :=
  ([12409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block100Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12409
    = surrogateDiagTailX0RatChunk000Sub001Block100Part012

theorem surrogateDiagonalTailChunk000Sub001Block100Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part012] using hcert

def TailChunk000Sub001Block100Part013SupportExplicit : Finset ℕ :=
  ([12410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part013 : ℚ :=
  (1679894405575 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub001Block100Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12410
    = surrogateDiagTailX0RatChunk000Sub001Block100Part013

theorem surrogateDiagonalTailChunk000Sub001Block100Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part013] using hcert

def TailChunk000Sub001Block100Part014SupportExplicit : Finset ℕ :=
  ([12413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block100Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12413
    = surrogateDiagTailX0RatChunk000Sub001Block100Part014

theorem surrogateDiagonalTailChunk000Sub001Block100Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part014] using hcert

def TailChunk000Sub001Block100Part015SupportExplicit : Finset ℕ :=
  ([12414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part015 : ℚ :=
  (160435875 : ℚ) / 73158051349504

def SurrogateDiagonalTailChunk000Sub001Block100Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12414
    = surrogateDiagTailX0RatChunk000Sub001Block100Part015

theorem surrogateDiagonalTailChunk000Sub001Block100Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part015] using hcert

def TailChunk000Sub001Block100Part016SupportExplicit : Finset ℕ :=
  ([12415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part016 : ℚ :=
  (17761048277 : ℚ) / 345968220576153600

def SurrogateDiagonalTailChunk000Sub001Block100Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12415
    = surrogateDiagTailX0RatChunk000Sub001Block100Part016

theorem surrogateDiagonalTailChunk000Sub001Block100Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part016] using hcert

def TailChunk000Sub001Block100Part017SupportExplicit : Finset ℕ :=
  ([12417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part017 : ℚ :=
  (1070288567525 : ℚ) / 5865145511062023744

def SurrogateDiagonalTailChunk000Sub001Block100Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12417
    = surrogateDiagTailX0RatChunk000Sub001Block100Part017

theorem surrogateDiagonalTailChunk000Sub001Block100Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part017] using hcert

def TailChunk000Sub001Block100Part018SupportExplicit : Finset ℕ :=
  ([12418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part018 : ℚ :=
  (2013816908575 : ℚ) / 1996947962582410368

def SurrogateDiagonalTailChunk000Sub001Block100Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12418
    = surrogateDiagTailX0RatChunk000Sub001Block100Part018

theorem surrogateDiagonalTailChunk000Sub001Block100Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part018] using hcert

def TailChunk000Sub001Block100Part019SupportExplicit : Finset ℕ :=
  ([12419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part019 : ℚ :=
  (66738137 : ℚ) / 6747020148602880

def SurrogateDiagonalTailChunk000Sub001Block100Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12419
    = surrogateDiagTailX0RatChunk000Sub001Block100Part019

theorem surrogateDiagonalTailChunk000Sub001Block100Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part019] using hcert

def TailChunk000Sub001Block100Part020SupportExplicit : Finset ℕ :=
  ([12421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block100Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12421
    = surrogateDiagTailX0RatChunk000Sub001Block100Part020

theorem surrogateDiagonalTailChunk000Sub001Block100Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part020] using hcert

def TailChunk000Sub001Block100Part021SupportExplicit : Finset ℕ :=
  ([12422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part021 : ℚ :=
  (964413025 : ℚ) / 1487487246771762

def SurrogateDiagonalTailChunk000Sub001Block100Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12422
    = surrogateDiagTailX0RatChunk000Sub001Block100Part021

theorem surrogateDiagonalTailChunk000Sub001Block100Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part021] using hcert

def TailChunk000Sub001Block100Part022SupportExplicit : Finset ℕ :=
  ([12423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part022 : ℚ :=
  (43414401907 : ℚ) / 409681920000000000

def SurrogateDiagonalTailChunk000Sub001Block100Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12423
    = surrogateDiagTailX0RatChunk000Sub001Block100Part022

theorem surrogateDiagonalTailChunk000Sub001Block100Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part022] using hcert

def TailChunk000Sub001Block100Part023SupportExplicit : Finset ℕ :=
  ([12426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part023 : ℚ :=
  (627511952375 : ℚ) / 285694505605545984

def SurrogateDiagonalTailChunk000Sub001Block100Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12426
    = surrogateDiagTailX0RatChunk000Sub001Block100Part023

theorem surrogateDiagonalTailChunk000Sub001Block100Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part023] using hcert

def TailChunk000Sub001Block100Part024SupportExplicit : Finset ℕ :=
  ([12430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block100Part024 : ℚ :=
  (13028109131 : ℚ) / 8058030407024640

def SurrogateDiagonalTailChunk000Sub001Block100Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12430
    = surrogateDiagTailX0RatChunk000Sub001Block100Part024

theorem surrogateDiagonalTailChunk000Sub001Block100Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block100Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block100Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block100Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block100Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block100Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block100HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block100Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block100Part000
    + surrogateDiagTailX0RatChunk000Sub001Block100Part001
    + surrogateDiagTailX0RatChunk000Sub001Block100Part002
    + surrogateDiagTailX0RatChunk000Sub001Block100Part003
    + surrogateDiagTailX0RatChunk000Sub001Block100Part004
    + surrogateDiagTailX0RatChunk000Sub001Block100Part005
    + surrogateDiagTailX0RatChunk000Sub001Block100Part006
    + surrogateDiagTailX0RatChunk000Sub001Block100Part007
    + surrogateDiagTailX0RatChunk000Sub001Block100Part008
    + surrogateDiagTailX0RatChunk000Sub001Block100Part009

def surrogateDiagonalTailChunk000Sub001Block100MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block100Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block100Part010
    + surrogateDiagTailX0RatChunk000Sub001Block100Part011
    + surrogateDiagTailX0RatChunk000Sub001Block100Part012
    + surrogateDiagTailX0RatChunk000Sub001Block100Part013
    + surrogateDiagTailX0RatChunk000Sub001Block100Part014
    + surrogateDiagTailX0RatChunk000Sub001Block100Part015
    + surrogateDiagTailX0RatChunk000Sub001Block100Part016
    + surrogateDiagTailX0RatChunk000Sub001Block100Part017
    + surrogateDiagTailX0RatChunk000Sub001Block100Part018
    + surrogateDiagTailX0RatChunk000Sub001Block100Part019

def surrogateDiagonalTailChunk000Sub001Block100TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block100Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block100Part020
    + surrogateDiagTailX0RatChunk000Sub001Block100Part021
    + surrogateDiagTailX0RatChunk000Sub001Block100Part022
    + surrogateDiagTailX0RatChunk000Sub001Block100Part023
    + surrogateDiagTailX0RatChunk000Sub001Block100Part024

def surrogateDiagonalTailChunk000Sub001Block100Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block100HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block100MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block100TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block100 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block100Part000
    + surrogateDiagTailX0RatChunk000Sub001Block100Part001
    + surrogateDiagTailX0RatChunk000Sub001Block100Part002
    + surrogateDiagTailX0RatChunk000Sub001Block100Part003
    + surrogateDiagTailX0RatChunk000Sub001Block100Part004
    + surrogateDiagTailX0RatChunk000Sub001Block100Part005
    + surrogateDiagTailX0RatChunk000Sub001Block100Part006
    + surrogateDiagTailX0RatChunk000Sub001Block100Part007
    + surrogateDiagTailX0RatChunk000Sub001Block100Part008
    + surrogateDiagTailX0RatChunk000Sub001Block100Part009
    + surrogateDiagTailX0RatChunk000Sub001Block100Part010
    + surrogateDiagTailX0RatChunk000Sub001Block100Part011
    + surrogateDiagTailX0RatChunk000Sub001Block100Part012
    + surrogateDiagTailX0RatChunk000Sub001Block100Part013
    + surrogateDiagTailX0RatChunk000Sub001Block100Part014
    + surrogateDiagTailX0RatChunk000Sub001Block100Part015
    + surrogateDiagTailX0RatChunk000Sub001Block100Part016
    + surrogateDiagTailX0RatChunk000Sub001Block100Part017
    + surrogateDiagTailX0RatChunk000Sub001Block100Part018
    + surrogateDiagTailX0RatChunk000Sub001Block100Part019
    + surrogateDiagTailX0RatChunk000Sub001Block100Part020
    + surrogateDiagTailX0RatChunk000Sub001Block100Part021
    + surrogateDiagTailX0RatChunk000Sub001Block100Part022
    + surrogateDiagTailX0RatChunk000Sub001Block100Part023
    + surrogateDiagTailX0RatChunk000Sub001Block100Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block100_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block100Head + surrogateDiagTailX0RatChunk000Sub001Block100Mid + surrogateDiagTailX0RatChunk000Sub001Block100Tail =
      surrogateDiagTailX0RatChunk000Sub001Block100 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block100Head surrogateDiagTailX0RatChunk000Sub001Block100Mid surrogateDiagTailX0RatChunk000Sub001Block100Tail surrogateDiagTailX0RatChunk000Sub001Block100
  ring

def SurrogateDiagonalTailChunk000Sub001Block100HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block100HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block100Head

def SurrogateDiagonalTailChunk000Sub001Block100MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block100MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block100Mid

def SurrogateDiagonalTailChunk000Sub001Block100TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block100TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block100Tail

theorem surrogateDiagonalTailChunk000Sub001Block100_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block100HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block100MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block100TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block100Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block100 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block100HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block100MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block100TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block100Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block100_eq_head_add_mid_add_tail

/-- Block 101 covers tail-support indices [7525,7550) and q from 12431 to 12471. -/

def TailChunk000Sub001Block101Part000SupportExplicit : Finset ℕ :=
  ([12431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part000 : ℚ :=
  (5561896759 : ℚ) / 2074014720000000000

def SurrogateDiagonalTailChunk000Sub001Block101Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12431
    = surrogateDiagTailX0RatChunk000Sub001Block101Part000

theorem surrogateDiagonalTailChunk000Sub001Block101Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part000] using hcert

def TailChunk000Sub001Block101Part001SupportExplicit : Finset ℕ :=
  ([12433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block101Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12433
    = surrogateDiagTailX0RatChunk000Sub001Block101Part001

theorem surrogateDiagonalTailChunk000Sub001Block101Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part001] using hcert

def TailChunk000Sub001Block101Part002SupportExplicit : Finset ℕ :=
  ([12434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part002 : ℚ :=
  (603923265625 : ℚ) / 933277704146145792

def SurrogateDiagonalTailChunk000Sub001Block101Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12434
    = surrogateDiagTailX0RatChunk000Sub001Block101Part002

theorem surrogateDiagonalTailChunk000Sub001Block101Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part002] using hcert

def TailChunk000Sub001Block101Part003SupportExplicit : Finset ℕ :=
  ([12435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part003 : ℚ :=
  (1159439593975 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk000Sub001Block101Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12435
    = surrogateDiagTailX0RatChunk000Sub001Block101Part003

theorem surrogateDiagonalTailChunk000Sub001Block101Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part003] using hcert

def TailChunk000Sub001Block101Part004SupportExplicit : Finset ℕ :=
  ([12437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block101Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12437
    = surrogateDiagTailX0RatChunk000Sub001Block101Part004

theorem surrogateDiagonalTailChunk000Sub001Block101Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part004] using hcert

def TailChunk000Sub001Block101Part005SupportExplicit : Finset ℕ :=
  ([12439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part005 : ℚ :=
  (10982334475 : ℚ) / 597048960253427712

def SurrogateDiagonalTailChunk000Sub001Block101Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12439
    = surrogateDiagTailX0RatChunk000Sub001Block101Part005

theorem surrogateDiagonalTailChunk000Sub001Block101Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part005] using hcert

def TailChunk000Sub001Block101Part006SupportExplicit : Finset ℕ :=
  ([12441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part006 : ℚ :=
  (11107489429 : ℚ) / 50992223669452800

def SurrogateDiagonalTailChunk000Sub001Block101Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12441
    = surrogateDiagTailX0RatChunk000Sub001Block101Part006

theorem surrogateDiagonalTailChunk000Sub001Block101Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part006] using hcert

def TailChunk000Sub001Block101Part007SupportExplicit : Finset ℕ :=
  ([12442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part007 : ℚ :=
  (967521025 : ℚ) / 1497091653018912

def SurrogateDiagonalTailChunk000Sub001Block101Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12442
    = surrogateDiagTailX0RatChunk000Sub001Block101Part007

theorem surrogateDiagonalTailChunk000Sub001Block101Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part007] using hcert

def TailChunk000Sub001Block101Part008SupportExplicit : Finset ℕ :=
  ([12443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part008 : ℚ :=
  (6825069661 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk000Sub001Block101Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12443
    = surrogateDiagTailX0RatChunk000Sub001Block101Part008

theorem surrogateDiagonalTailChunk000Sub001Block101Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part008] using hcert

def TailChunk000Sub001Block101Part009SupportExplicit : Finset ℕ :=
  ([12445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part009 : ℚ :=
  (570369197 : ℚ) / 12794961834270720

def SurrogateDiagonalTailChunk000Sub001Block101Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12445
    = surrogateDiagTailX0RatChunk000Sub001Block101Part009

theorem surrogateDiagonalTailChunk000Sub001Block101Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part009] using hcert

def TailChunk000Sub001Block101Part010SupportExplicit : Finset ℕ :=
  ([12449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part010 : ℚ :=
  (240061541 : ℚ) / 157234544804836800

def SurrogateDiagonalTailChunk000Sub001Block101Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12449
    = surrogateDiagTailX0RatChunk000Sub001Block101Part010

theorem surrogateDiagonalTailChunk000Sub001Block101Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part010] using hcert

def TailChunk000Sub001Block101Part011SupportExplicit : Finset ℕ :=
  ([12451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block101Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12451
    = surrogateDiagTailX0RatChunk000Sub001Block101Part011

theorem surrogateDiagonalTailChunk000Sub001Block101Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part011] using hcert

def TailChunk000Sub001Block101Part012SupportExplicit : Finset ℕ :=
  ([12453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part012 : ℚ :=
  (538573665275 : ℚ) / 3184261121351614464

def SurrogateDiagonalTailChunk000Sub001Block101Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12453
    = surrogateDiagTailX0RatChunk000Sub001Block101Part012

theorem surrogateDiagonalTailChunk000Sub001Block101Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part012] using hcert

def TailChunk000Sub001Block101Part013SupportExplicit : Finset ℕ :=
  ([12454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part013 : ℚ :=
  (734443859675 : ℚ) / 902281753330292736

def SurrogateDiagonalTailChunk000Sub001Block101Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12454
    = surrogateDiagTailX0RatChunk000Sub001Block101Part013

theorem surrogateDiagonalTailChunk000Sub001Block101Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part013] using hcert

def TailChunk000Sub001Block101Part014SupportExplicit : Finset ℕ :=
  ([12455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part014 : ℚ :=
  (417783509375 : ℚ) / 10478075653338169344

def SurrogateDiagonalTailChunk000Sub001Block101Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12455
    = surrogateDiagTailX0RatChunk000Sub001Block101Part014

theorem surrogateDiagonalTailChunk000Sub001Block101Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part014] using hcert

def TailChunk000Sub001Block101Part015SupportExplicit : Finset ℕ :=
  ([12457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block101Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12457
    = surrogateDiagTailX0RatChunk000Sub001Block101Part015

theorem surrogateDiagonalTailChunk000Sub001Block101Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part015] using hcert

def TailChunk000Sub001Block101Part016SupportExplicit : Finset ℕ :=
  ([12458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part016 : ℚ :=
  (606256890625 : ℚ) / 940505377703008032

def SurrogateDiagonalTailChunk000Sub001Block101Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12458
    = surrogateDiagTailX0RatChunk000Sub001Block101Part016

theorem surrogateDiagonalTailChunk000Sub001Block101Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part016] using hcert

def TailChunk000Sub001Block101Part017SupportExplicit : Finset ℕ :=
  ([12459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part017 : ℚ :=
  (269517270925 : ℚ) / 2972461440641605632

def SurrogateDiagonalTailChunk000Sub001Block101Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12459
    = surrogateDiagTailX0RatChunk000Sub001Block101Part017

theorem surrogateDiagonalTailChunk000Sub001Block101Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part017] using hcert

def TailChunk000Sub001Block101Part018SupportExplicit : Finset ℕ :=
  ([12461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part018 : ℚ :=
  (11429530475 : ℚ) / 2613837646031486976

def SurrogateDiagonalTailChunk000Sub001Block101Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12461
    = surrogateDiagTailX0RatChunk000Sub001Block101Part018

theorem surrogateDiagonalTailChunk000Sub001Block101Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part018] using hcert

def TailChunk000Sub001Block101Part019SupportExplicit : Finset ℕ :=
  ([12462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part019 : ℚ :=
  (61123469269 : ℚ) / 24596176107571200

def SurrogateDiagonalTailChunk000Sub001Block101Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12462
    = surrogateDiagTailX0RatChunk000Sub001Block101Part019

theorem surrogateDiagonalTailChunk000Sub001Block101Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part019] using hcert

def TailChunk000Sub001Block101Part020SupportExplicit : Finset ℕ :=
  ([12466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part020 : ℚ :=
  (3392515259 : ℚ) / 4611783020169600

def SurrogateDiagonalTailChunk000Sub001Block101Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12466
    = surrogateDiagTailX0RatChunk000Sub001Block101Part020

theorem surrogateDiagonalTailChunk000Sub001Block101Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part020] using hcert

def TailChunk000Sub001Block101Part021SupportExplicit : Finset ℕ :=
  ([12467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part021 : ℚ :=
  (23853347825 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk000Sub001Block101Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12467
    = surrogateDiagTailX0RatChunk000Sub001Block101Part021

theorem surrogateDiagonalTailChunk000Sub001Block101Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part021] using hcert

def TailChunk000Sub001Block101Part022SupportExplicit : Finset ℕ :=
  ([12469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part022 : ℚ :=
  (4325294375 : ℚ) / 1982577656268324864

def SurrogateDiagonalTailChunk000Sub001Block101Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12469
    = surrogateDiagTailX0RatChunk000Sub001Block101Part022

theorem surrogateDiagonalTailChunk000Sub001Block101Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part022] using hcert

def TailChunk000Sub001Block101Part023SupportExplicit : Finset ℕ :=
  ([12470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part023 : ℚ :=
  (215216779025 : ℚ) / 612161645151780864

def SurrogateDiagonalTailChunk000Sub001Block101Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12470
    = surrogateDiagTailX0RatChunk000Sub001Block101Part023

theorem surrogateDiagonalTailChunk000Sub001Block101Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part023] using hcert

def TailChunk000Sub001Block101Part024SupportExplicit : Finset ℕ :=
  ([12471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block101Part024 : ℚ :=
  (67509130225 : ℚ) / 745983144037688448

def SurrogateDiagonalTailChunk000Sub001Block101Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12471
    = surrogateDiagTailX0RatChunk000Sub001Block101Part024

theorem surrogateDiagonalTailChunk000Sub001Block101Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block101Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block101Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block101Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block101Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block101Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block101HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block101Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block101Part000
    + surrogateDiagTailX0RatChunk000Sub001Block101Part001
    + surrogateDiagTailX0RatChunk000Sub001Block101Part002
    + surrogateDiagTailX0RatChunk000Sub001Block101Part003
    + surrogateDiagTailX0RatChunk000Sub001Block101Part004
    + surrogateDiagTailX0RatChunk000Sub001Block101Part005
    + surrogateDiagTailX0RatChunk000Sub001Block101Part006
    + surrogateDiagTailX0RatChunk000Sub001Block101Part007
    + surrogateDiagTailX0RatChunk000Sub001Block101Part008
    + surrogateDiagTailX0RatChunk000Sub001Block101Part009

def surrogateDiagonalTailChunk000Sub001Block101MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block101Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block101Part010
    + surrogateDiagTailX0RatChunk000Sub001Block101Part011
    + surrogateDiagTailX0RatChunk000Sub001Block101Part012
    + surrogateDiagTailX0RatChunk000Sub001Block101Part013
    + surrogateDiagTailX0RatChunk000Sub001Block101Part014
    + surrogateDiagTailX0RatChunk000Sub001Block101Part015
    + surrogateDiagTailX0RatChunk000Sub001Block101Part016
    + surrogateDiagTailX0RatChunk000Sub001Block101Part017
    + surrogateDiagTailX0RatChunk000Sub001Block101Part018
    + surrogateDiagTailX0RatChunk000Sub001Block101Part019

def surrogateDiagonalTailChunk000Sub001Block101TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block101Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block101Part020
    + surrogateDiagTailX0RatChunk000Sub001Block101Part021
    + surrogateDiagTailX0RatChunk000Sub001Block101Part022
    + surrogateDiagTailX0RatChunk000Sub001Block101Part023
    + surrogateDiagTailX0RatChunk000Sub001Block101Part024

def surrogateDiagonalTailChunk000Sub001Block101Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block101HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block101MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block101TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block101 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block101Part000
    + surrogateDiagTailX0RatChunk000Sub001Block101Part001
    + surrogateDiagTailX0RatChunk000Sub001Block101Part002
    + surrogateDiagTailX0RatChunk000Sub001Block101Part003
    + surrogateDiagTailX0RatChunk000Sub001Block101Part004
    + surrogateDiagTailX0RatChunk000Sub001Block101Part005
    + surrogateDiagTailX0RatChunk000Sub001Block101Part006
    + surrogateDiagTailX0RatChunk000Sub001Block101Part007
    + surrogateDiagTailX0RatChunk000Sub001Block101Part008
    + surrogateDiagTailX0RatChunk000Sub001Block101Part009
    + surrogateDiagTailX0RatChunk000Sub001Block101Part010
    + surrogateDiagTailX0RatChunk000Sub001Block101Part011
    + surrogateDiagTailX0RatChunk000Sub001Block101Part012
    + surrogateDiagTailX0RatChunk000Sub001Block101Part013
    + surrogateDiagTailX0RatChunk000Sub001Block101Part014
    + surrogateDiagTailX0RatChunk000Sub001Block101Part015
    + surrogateDiagTailX0RatChunk000Sub001Block101Part016
    + surrogateDiagTailX0RatChunk000Sub001Block101Part017
    + surrogateDiagTailX0RatChunk000Sub001Block101Part018
    + surrogateDiagTailX0RatChunk000Sub001Block101Part019
    + surrogateDiagTailX0RatChunk000Sub001Block101Part020
    + surrogateDiagTailX0RatChunk000Sub001Block101Part021
    + surrogateDiagTailX0RatChunk000Sub001Block101Part022
    + surrogateDiagTailX0RatChunk000Sub001Block101Part023
    + surrogateDiagTailX0RatChunk000Sub001Block101Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block101_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block101Head + surrogateDiagTailX0RatChunk000Sub001Block101Mid + surrogateDiagTailX0RatChunk000Sub001Block101Tail =
      surrogateDiagTailX0RatChunk000Sub001Block101 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block101Head surrogateDiagTailX0RatChunk000Sub001Block101Mid surrogateDiagTailX0RatChunk000Sub001Block101Tail surrogateDiagTailX0RatChunk000Sub001Block101
  ring

def SurrogateDiagonalTailChunk000Sub001Block101HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block101HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block101Head

def SurrogateDiagonalTailChunk000Sub001Block101MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block101MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block101Mid

def SurrogateDiagonalTailChunk000Sub001Block101TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block101TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block101Tail

theorem surrogateDiagonalTailChunk000Sub001Block101_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block101HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block101MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block101TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block101Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block101 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block101HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block101MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block101TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block101Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block101_eq_head_add_mid_add_tail

/-- Block 102 covers tail-support indices [7550,7575) and q from 12473 to 12517. -/

def TailChunk000Sub001Block102Part000SupportExplicit : Finset ℕ :=
  ([12473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block102Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12473
    = surrogateDiagTailX0RatChunk000Sub001Block102Part000

theorem surrogateDiagonalTailChunk000Sub001Block102Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part000] using hcert

def TailChunk000Sub001Block102Part001SupportExplicit : Finset ℕ :=
  ([12477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part001 : ℚ :=
  (77227523825 : ℚ) / 854194450995813312

def SurrogateDiagonalTailChunk000Sub001Block102Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12477
    = surrogateDiagTailX0RatChunk000Sub001Block102Part001

theorem surrogateDiagonalTailChunk000Sub001Block102Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part001] using hcert

def TailChunk000Sub001Block102Part002SupportExplicit : Finset ℕ :=
  ([12478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part002 : ℚ :=
  (60951825725 : ℚ) / 1470283675892711424

def SurrogateDiagonalTailChunk000Sub001Block102Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12478
    = surrogateDiagTailX0RatChunk000Sub001Block102Part002

theorem surrogateDiagonalTailChunk000Sub001Block102Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part002] using hcert

def TailChunk000Sub001Block102Part003SupportExplicit : Finset ℕ :=
  ([12479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block102Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12479
    = surrogateDiagTailX0RatChunk000Sub001Block102Part003

theorem surrogateDiagonalTailChunk000Sub001Block102Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part003] using hcert

def TailChunk000Sub001Block102Part004SupportExplicit : Finset ℕ :=
  ([12481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part004 : ℚ :=
  (11056429825 : ℚ) / 605158167906654912

def SurrogateDiagonalTailChunk000Sub001Block102Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12481
    = surrogateDiagTailX0RatChunk000Sub001Block102Part004

theorem surrogateDiagonalTailChunk000Sub001Block102Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part004] using hcert

def TailChunk000Sub001Block102Part005SupportExplicit : Finset ℕ :=
  ([12485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part005 : ℚ :=
  (241666353 : ℚ) / 4453170393694208

def SurrogateDiagonalTailChunk000Sub001Block102Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12485
    = surrogateDiagTailX0RatChunk000Sub001Block102Part005

theorem surrogateDiagonalTailChunk000Sub001Block102Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part005] using hcert

def TailChunk000Sub001Block102Part006SupportExplicit : Finset ℕ :=
  ([12486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part006 : ℚ :=
  (10826335139 : ℚ) / 14977184405913600

def SurrogateDiagonalTailChunk000Sub001Block102Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12486
    = surrogateDiagTailX0RatChunk000Sub001Block102Part006

theorem surrogateDiagonalTailChunk000Sub001Block102Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part006] using hcert

def TailChunk000Sub001Block102Part007SupportExplicit : Finset ℕ :=
  ([12487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block102Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12487
    = surrogateDiagTailX0RatChunk000Sub001Block102Part007

theorem surrogateDiagonalTailChunk000Sub001Block102Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part007] using hcert

def TailChunk000Sub001Block102Part008SupportExplicit : Finset ℕ :=
  ([12489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part008 : ℚ :=
  (22183119749 : ℚ) / 196769408860569600

def SurrogateDiagonalTailChunk000Sub001Block102Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12489
    = surrogateDiagTailX0RatChunk000Sub001Block102Part008

theorem surrogateDiagonalTailChunk000Sub001Block102Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part008] using hcert

def TailChunk000Sub001Block102Part009SupportExplicit : Finset ℕ :=
  ([12490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part009 : ℚ :=
  (195196187675 : ℚ) / 776417239602561024

def SurrogateDiagonalTailChunk000Sub001Block102Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12490
    = surrogateDiagTailX0RatChunk000Sub001Block102Part009

theorem surrogateDiagonalTailChunk000Sub001Block102Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part009] using hcert

def TailChunk000Sub001Block102Part010SupportExplicit : Finset ℕ :=
  ([12491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block102Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12491
    = surrogateDiagTailX0RatChunk000Sub001Block102Part010

theorem surrogateDiagonalTailChunk000Sub001Block102Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part010] using hcert

def TailChunk000Sub001Block102Part011SupportExplicit : Finset ℕ :=
  ([12494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block102Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12494
    = surrogateDiagTailX0RatChunk000Sub001Block102Part011

theorem surrogateDiagonalTailChunk000Sub001Block102Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part011] using hcert

def TailChunk000Sub001Block102Part012SupportExplicit : Finset ℕ :=
  ([12497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block102Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12497
    = surrogateDiagTailX0RatChunk000Sub001Block102Part012

theorem surrogateDiagonalTailChunk000Sub001Block102Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part012] using hcert

def TailChunk000Sub001Block102Part013SupportExplicit : Finset ℕ :=
  ([12498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part013 : ℚ :=
  (271178524325 : ℚ) / 375871802452144704

def SurrogateDiagonalTailChunk000Sub001Block102Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12498
    = surrogateDiagTailX0RatChunk000Sub001Block102Part013

theorem surrogateDiagonalTailChunk000Sub001Block102Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part013] using hcert

def TailChunk000Sub001Block102Part014SupportExplicit : Finset ℕ :=
  ([12499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part014 : ℚ :=
  (258277371 : ℚ) / 100086039274547200

def SurrogateDiagonalTailChunk000Sub001Block102Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12499
    = surrogateDiagTailX0RatChunk000Sub001Block102Part014

theorem surrogateDiagonalTailChunk000Sub001Block102Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part014] using hcert

def TailChunk000Sub001Block102Part015SupportExplicit : Finset ℕ :=
  ([12502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part015 : ℚ :=
  (1867656569575 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub001Block102Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12502
    = surrogateDiagTailX0RatChunk000Sub001Block102Part015

theorem surrogateDiagonalTailChunk000Sub001Block102Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part015] using hcert

def TailChunk000Sub001Block102Part016SupportExplicit : Finset ℕ :=
  ([12503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part016 : ℚ :=
  (2442578265625 : ℚ) / 15271610742906310002

def SurrogateDiagonalTailChunk000Sub001Block102Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12503
    = surrogateDiagTailX0RatChunk000Sub001Block102Part016

theorem surrogateDiagonalTailChunk000Sub001Block102Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part016] using hcert

def TailChunk000Sub001Block102Part017SupportExplicit : Finset ℕ :=
  ([12505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part017 : ℚ :=
  (124736616677 : ℚ) / 424758214656000000

def SurrogateDiagonalTailChunk000Sub001Block102Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12505
    = surrogateDiagTailX0RatChunk000Sub001Block102Part017

theorem surrogateDiagonalTailChunk000Sub001Block102Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part017] using hcert

def TailChunk000Sub001Block102Part018SupportExplicit : Finset ℕ :=
  ([12507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part018 : ℚ :=
  (467754085 : ℚ) / 816796824939648

def SurrogateDiagonalTailChunk000Sub001Block102Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12507
    = surrogateDiagTailX0RatChunk000Sub001Block102Part018

theorem surrogateDiagonalTailChunk000Sub001Block102Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part018] using hcert

def TailChunk000Sub001Block102Part019SupportExplicit : Finset ℕ :=
  ([12509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part019 : ℚ :=
  (118414279375 : ℚ) / 515202194991841362

def SurrogateDiagonalTailChunk000Sub001Block102Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12509
    = surrogateDiagTailX0RatChunk000Sub001Block102Part019

theorem surrogateDiagonalTailChunk000Sub001Block102Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part019] using hcert

def TailChunk000Sub001Block102Part020SupportExplicit : Finset ℕ :=
  ([12511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part020 : ℚ :=
  (3913128025 : ℚ) / 24497179756270002

def SurrogateDiagonalTailChunk000Sub001Block102Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12511
    = surrogateDiagTailX0RatChunk000Sub001Block102Part020

theorem surrogateDiagonalTailChunk000Sub001Block102Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part020] using hcert

def TailChunk000Sub001Block102Part021SupportExplicit : Finset ℕ :=
  ([12513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part021 : ℚ :=
  (5163424451125 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block102Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12513
    = surrogateDiagTailX0RatChunk000Sub001Block102Part021

theorem surrogateDiagonalTailChunk000Sub001Block102Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part021] using hcert

def TailChunk000Sub001Block102Part022SupportExplicit : Finset ℕ :=
  ([12514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part022 : ℚ :=
  (611719515625 : ℚ) / 957533170935078912

def SurrogateDiagonalTailChunk000Sub001Block102Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12514
    = surrogateDiagTailX0RatChunk000Sub001Block102Part022

theorem surrogateDiagonalTailChunk000Sub001Block102Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part022] using hcert

def TailChunk000Sub001Block102Part023SupportExplicit : Finset ℕ :=
  ([12515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part023 : ℚ :=
  (6653130625525 : ℚ) / 25085112070420482048

def SurrogateDiagonalTailChunk000Sub001Block102Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12515
    = surrogateDiagTailX0RatChunk000Sub001Block102Part023

theorem surrogateDiagonalTailChunk000Sub001Block102Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part023] using hcert

def TailChunk000Sub001Block102Part024SupportExplicit : Finset ℕ :=
  ([12517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block102Part024 : ℚ :=
  (2448051390625 : ℚ) / 15340131603379068192

def SurrogateDiagonalTailChunk000Sub001Block102Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12517
    = surrogateDiagTailX0RatChunk000Sub001Block102Part024

theorem surrogateDiagonalTailChunk000Sub001Block102Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block102Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block102Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block102Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block102Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block102Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block102HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block102Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block102Part000
    + surrogateDiagTailX0RatChunk000Sub001Block102Part001
    + surrogateDiagTailX0RatChunk000Sub001Block102Part002
    + surrogateDiagTailX0RatChunk000Sub001Block102Part003
    + surrogateDiagTailX0RatChunk000Sub001Block102Part004
    + surrogateDiagTailX0RatChunk000Sub001Block102Part005
    + surrogateDiagTailX0RatChunk000Sub001Block102Part006
    + surrogateDiagTailX0RatChunk000Sub001Block102Part007
    + surrogateDiagTailX0RatChunk000Sub001Block102Part008
    + surrogateDiagTailX0RatChunk000Sub001Block102Part009

def surrogateDiagonalTailChunk000Sub001Block102MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block102Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block102Part010
    + surrogateDiagTailX0RatChunk000Sub001Block102Part011
    + surrogateDiagTailX0RatChunk000Sub001Block102Part012
    + surrogateDiagTailX0RatChunk000Sub001Block102Part013
    + surrogateDiagTailX0RatChunk000Sub001Block102Part014
    + surrogateDiagTailX0RatChunk000Sub001Block102Part015
    + surrogateDiagTailX0RatChunk000Sub001Block102Part016
    + surrogateDiagTailX0RatChunk000Sub001Block102Part017
    + surrogateDiagTailX0RatChunk000Sub001Block102Part018
    + surrogateDiagTailX0RatChunk000Sub001Block102Part019

def surrogateDiagonalTailChunk000Sub001Block102TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block102Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block102Part020
    + surrogateDiagTailX0RatChunk000Sub001Block102Part021
    + surrogateDiagTailX0RatChunk000Sub001Block102Part022
    + surrogateDiagTailX0RatChunk000Sub001Block102Part023
    + surrogateDiagTailX0RatChunk000Sub001Block102Part024

def surrogateDiagonalTailChunk000Sub001Block102Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block102HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block102MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block102TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block102 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block102Part000
    + surrogateDiagTailX0RatChunk000Sub001Block102Part001
    + surrogateDiagTailX0RatChunk000Sub001Block102Part002
    + surrogateDiagTailX0RatChunk000Sub001Block102Part003
    + surrogateDiagTailX0RatChunk000Sub001Block102Part004
    + surrogateDiagTailX0RatChunk000Sub001Block102Part005
    + surrogateDiagTailX0RatChunk000Sub001Block102Part006
    + surrogateDiagTailX0RatChunk000Sub001Block102Part007
    + surrogateDiagTailX0RatChunk000Sub001Block102Part008
    + surrogateDiagTailX0RatChunk000Sub001Block102Part009
    + surrogateDiagTailX0RatChunk000Sub001Block102Part010
    + surrogateDiagTailX0RatChunk000Sub001Block102Part011
    + surrogateDiagTailX0RatChunk000Sub001Block102Part012
    + surrogateDiagTailX0RatChunk000Sub001Block102Part013
    + surrogateDiagTailX0RatChunk000Sub001Block102Part014
    + surrogateDiagTailX0RatChunk000Sub001Block102Part015
    + surrogateDiagTailX0RatChunk000Sub001Block102Part016
    + surrogateDiagTailX0RatChunk000Sub001Block102Part017
    + surrogateDiagTailX0RatChunk000Sub001Block102Part018
    + surrogateDiagTailX0RatChunk000Sub001Block102Part019
    + surrogateDiagTailX0RatChunk000Sub001Block102Part020
    + surrogateDiagTailX0RatChunk000Sub001Block102Part021
    + surrogateDiagTailX0RatChunk000Sub001Block102Part022
    + surrogateDiagTailX0RatChunk000Sub001Block102Part023
    + surrogateDiagTailX0RatChunk000Sub001Block102Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block102_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block102Head + surrogateDiagTailX0RatChunk000Sub001Block102Mid + surrogateDiagTailX0RatChunk000Sub001Block102Tail =
      surrogateDiagTailX0RatChunk000Sub001Block102 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block102Head surrogateDiagTailX0RatChunk000Sub001Block102Mid surrogateDiagTailX0RatChunk000Sub001Block102Tail surrogateDiagTailX0RatChunk000Sub001Block102
  ring

def SurrogateDiagonalTailChunk000Sub001Block102HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block102HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block102Head

def SurrogateDiagonalTailChunk000Sub001Block102MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block102MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block102Mid

def SurrogateDiagonalTailChunk000Sub001Block102TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block102TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block102Tail

theorem surrogateDiagonalTailChunk000Sub001Block102_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block102HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block102MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block102TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block102Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block102 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block102HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block102MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block102TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block102Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block102_eq_head_add_mid_add_tail

/-- Block 103 covers tail-support indices [7575,7600) and q from 12518 to 12558. -/

def TailChunk000Sub001Block103Part000SupportExplicit : Finset ℕ :=
  ([12518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part000 : ℚ :=
  (29083376229 : ℚ) / 34702354208358400

def SurrogateDiagonalTailChunk000Sub001Block103Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12518
    = surrogateDiagTailX0RatChunk000Sub001Block103Part000

theorem surrogateDiagonalTailChunk000Sub001Block103Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part000] using hcert

def TailChunk000Sub001Block103Part001SupportExplicit : Finset ℕ :=
  ([12521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part001 : ℚ :=
  (1280525553025 : ℚ) / 7029467279573768064

def SurrogateDiagonalTailChunk000Sub001Block103Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12521
    = surrogateDiagTailX0RatChunk000Sub001Block103Part001

theorem surrogateDiagonalTailChunk000Sub001Block103Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part001] using hcert

def TailChunk000Sub001Block103Part002SupportExplicit : Finset ℕ :=
  ([12522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part002 : ℚ :=
  (340163426275 : ℚ) / 189384340782457632

def SurrogateDiagonalTailChunk000Sub001Block103Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12522
    = surrogateDiagTailX0RatChunk000Sub001Block103Part002

theorem surrogateDiagonalTailChunk000Sub001Block103Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part002] using hcert

def TailChunk000Sub001Block103Part003SupportExplicit : Finset ℕ :=
  ([12523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part003 : ℚ :=
  (1898873086075 : ℚ) / 8280220973752300032

def SurrogateDiagonalTailChunk000Sub001Block103Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12523
    = surrogateDiagTailX0RatChunk000Sub001Block103Part003

theorem surrogateDiagonalTailChunk000Sub001Block103Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part003] using hcert

def TailChunk000Sub001Block103Part004SupportExplicit : Finset ℕ :=
  ([12526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part004 : ℚ :=
  (612893265625 : ℚ) / 961211859850393842

def SurrogateDiagonalTailChunk000Sub001Block103Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12526
    = surrogateDiagTailX0RatChunk000Sub001Block103Part004

theorem surrogateDiagonalTailChunk000Sub001Block103Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part004] using hcert

def TailChunk000Sub001Block103Part005SupportExplicit : Finset ℕ :=
  ([12527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part005 : ℚ :=
  (2451964515625 : ℚ) / 15389216058551767122

def SurrogateDiagonalTailChunk000Sub001Block103Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12527
    = surrogateDiagTailX0RatChunk000Sub001Block103Part005

theorem surrogateDiagonalTailChunk000Sub001Block103Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part005] using hcert

def TailChunk000Sub001Block103Part006SupportExplicit : Finset ℕ :=
  ([12529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part006 : ℚ :=
  (299152369231 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk000Sub001Block103Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12529
    = surrogateDiagTailX0RatChunk000Sub001Block103Part006

theorem surrogateDiagonalTailChunk000Sub001Block103Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part006] using hcert

def TailChunk000Sub001Block103Part007SupportExplicit : Finset ℕ :=
  ([12530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part007 : ℚ :=
  (1558293527575 : ℚ) / 832821320958640128

def SurrogateDiagonalTailChunk000Sub001Block103Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12530
    = surrogateDiagTailX0RatChunk000Sub001Block103Part007

theorem surrogateDiagonalTailChunk000Sub001Block103Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part007] using hcert

def TailChunk000Sub001Block103Part008SupportExplicit : Finset ℕ :=
  ([12531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part008 : ℚ :=
  (4360368582325 : ℚ) / 12167148300214468608

def SurrogateDiagonalTailChunk000Sub001Block103Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12531
    = surrogateDiagTailX0RatChunk000Sub001Block103Part008

theorem surrogateDiagonalTailChunk000Sub001Block103Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part008] using hcert

def TailChunk000Sub001Block103Part009SupportExplicit : Finset ℕ :=
  ([12533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part009 : ℚ :=
  (95269152073 : ℚ) / 572331045820500000

def SurrogateDiagonalTailChunk000Sub001Block103Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12533
    = surrogateDiagTailX0RatChunk000Sub001Block103Part009

theorem surrogateDiagonalTailChunk000Sub001Block103Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part009] using hcert

def TailChunk000Sub001Block103Part010SupportExplicit : Finset ℕ :=
  ([12534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part010 : ℚ :=
  (681631436225 : ℚ) / 380223384381702144

def SurrogateDiagonalTailChunk000Sub001Block103Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12534
    = surrogateDiagTailX0RatChunk000Sub001Block103Part010

theorem surrogateDiagonalTailChunk000Sub001Block103Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part010] using hcert

def TailChunk000Sub001Block103Part011SupportExplicit : Finset ℕ :=
  ([12535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part011 : ℚ :=
  (6145482565975 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk000Sub001Block103Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12535
    = surrogateDiagTailX0RatChunk000Sub001Block103Part011

theorem surrogateDiagonalTailChunk000Sub001Block103Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part011] using hcert

def TailChunk000Sub001Block103Part012SupportExplicit : Finset ℕ :=
  ([12538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part012 : ℚ :=
  (614068140625 : ℚ) / 964901138298691872

def SurrogateDiagonalTailChunk000Sub001Block103Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12538
    = surrogateDiagTailX0RatChunk000Sub001Block103Part012

theorem surrogateDiagonalTailChunk000Sub001Block103Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part012] using hcert

def TailChunk000Sub001Block103Part013SupportExplicit : Finset ℕ :=
  ([12539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part013 : ℚ :=
  (2456664390625 : ℚ) / 15448272784052670642

def SurrogateDiagonalTailChunk000Sub001Block103Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12539
    = surrogateDiagTailX0RatChunk000Sub001Block103Part013

theorem surrogateDiagonalTailChunk000Sub001Block103Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part013] using hcert

def TailChunk000Sub001Block103Part014SupportExplicit : Finset ℕ :=
  ([12541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part014 : ℚ :=
  (3931917025 : ℚ) / 24733011315700512

def SurrogateDiagonalTailChunk000Sub001Block103Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12541
    = surrogateDiagTailX0RatChunk000Sub001Block103Part014

theorem surrogateDiagonalTailChunk000Sub001Block103Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part014] using hcert

def TailChunk000Sub001Block103Part015SupportExplicit : Finset ℕ :=
  ([12542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part015 : ℚ :=
  (983136025 : ℚ) / 1545813207231282

def SurrogateDiagonalTailChunk000Sub001Block103Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12542
    = surrogateDiagTailX0RatChunk000Sub001Block103Part015

theorem surrogateDiagonalTailChunk000Sub001Block103Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part015] using hcert

def TailChunk000Sub001Block103Part016SupportExplicit : Finset ℕ :=
  ([12543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part016 : ℚ :=
  (4153785602725 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block103Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12543
    = surrogateDiagTailX0RatChunk000Sub001Block103Part016

theorem surrogateDiagonalTailChunk000Sub001Block103Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part016] using hcert

def TailChunk000Sub001Block103Part017SupportExplicit : Finset ℕ :=
  ([12545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part017 : ℚ :=
  (1462252116175 : ℚ) / 4509586605622689792

def SurrogateDiagonalTailChunk000Sub001Block103Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12545
    = surrogateDiagTailX0RatChunk000Sub001Block103Part017

theorem surrogateDiagonalTailChunk000Sub001Block103Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part017] using hcert

def TailChunk000Sub001Block103Part018SupportExplicit : Finset ℕ :=
  ([12547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part018 : ℚ :=
  (2459800140625 : ℚ) / 15487738254063569682

def SurrogateDiagonalTailChunk000Sub001Block103Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12547
    = surrogateDiagTailX0RatChunk000Sub001Block103Part018

theorem surrogateDiagonalTailChunk000Sub001Block103Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part018] using hcert

def TailChunk000Sub001Block103Part019SupportExplicit : Finset ℕ :=
  ([12549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part019 : ℚ :=
  (2088873819875 : ℚ) / 5371293219443441664

def SurrogateDiagonalTailChunk000Sub001Block103Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12549
    = surrogateDiagTailX0RatChunk000Sub001Block103Part019

theorem surrogateDiagonalTailChunk000Sub001Block103Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part019] using hcert

def TailChunk000Sub001Block103Part020SupportExplicit : Finset ℕ :=
  ([12551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part020 : ℚ :=
  (64701846127 : ℚ) / 223198832504332800

def SurrogateDiagonalTailChunk000Sub001Block103Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12551
    = surrogateDiagTailX0RatChunk000Sub001Block103Part020

theorem surrogateDiagonalTailChunk000Sub001Block103Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part020] using hcert

def TailChunk000Sub001Block103Part021SupportExplicit : Finset ℕ :=
  ([12553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part021 : ℚ :=
  (2462153265625 : ℚ) / 15517386942886973952

def SurrogateDiagonalTailChunk000Sub001Block103Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12553
    = surrogateDiagTailX0RatChunk000Sub001Block103Part021

theorem surrogateDiagonalTailChunk000Sub001Block103Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part021] using hcert

def TailChunk000Sub001Block103Part022SupportExplicit : Finset ℕ :=
  ([12554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part022 : ℚ :=
  (615636390625 : ℚ) / 969836683930435872

def SurrogateDiagonalTailChunk000Sub001Block103Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12554
    = surrogateDiagTailX0RatChunk000Sub001Block103Part022

theorem surrogateDiagonalTailChunk000Sub001Block103Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part022] using hcert

def TailChunk000Sub001Block103Part023SupportExplicit : Finset ℕ :=
  ([12557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part023 : ℚ :=
  (1031415193175 : ℚ) / 5947732968804974592

def SurrogateDiagonalTailChunk000Sub001Block103Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12557
    = surrogateDiagTailX0RatChunk000Sub001Block103Part023

theorem surrogateDiagonalTailChunk000Sub001Block103Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part023] using hcert

def TailChunk000Sub001Block103Part024SupportExplicit : Finset ℕ :=
  ([12558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block103Part024 : ℚ :=
  (1162820890525 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub001Block103Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12558
    = surrogateDiagTailX0RatChunk000Sub001Block103Part024

theorem surrogateDiagonalTailChunk000Sub001Block103Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block103Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block103Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block103Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block103Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block103Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block103HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block103Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block103Part000
    + surrogateDiagTailX0RatChunk000Sub001Block103Part001
    + surrogateDiagTailX0RatChunk000Sub001Block103Part002
    + surrogateDiagTailX0RatChunk000Sub001Block103Part003
    + surrogateDiagTailX0RatChunk000Sub001Block103Part004
    + surrogateDiagTailX0RatChunk000Sub001Block103Part005
    + surrogateDiagTailX0RatChunk000Sub001Block103Part006
    + surrogateDiagTailX0RatChunk000Sub001Block103Part007
    + surrogateDiagTailX0RatChunk000Sub001Block103Part008
    + surrogateDiagTailX0RatChunk000Sub001Block103Part009

def surrogateDiagonalTailChunk000Sub001Block103MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block103Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block103Part010
    + surrogateDiagTailX0RatChunk000Sub001Block103Part011
    + surrogateDiagTailX0RatChunk000Sub001Block103Part012
    + surrogateDiagTailX0RatChunk000Sub001Block103Part013
    + surrogateDiagTailX0RatChunk000Sub001Block103Part014
    + surrogateDiagTailX0RatChunk000Sub001Block103Part015
    + surrogateDiagTailX0RatChunk000Sub001Block103Part016
    + surrogateDiagTailX0RatChunk000Sub001Block103Part017
    + surrogateDiagTailX0RatChunk000Sub001Block103Part018
    + surrogateDiagTailX0RatChunk000Sub001Block103Part019

def surrogateDiagonalTailChunk000Sub001Block103TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block103Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block103Part020
    + surrogateDiagTailX0RatChunk000Sub001Block103Part021
    + surrogateDiagTailX0RatChunk000Sub001Block103Part022
    + surrogateDiagTailX0RatChunk000Sub001Block103Part023
    + surrogateDiagTailX0RatChunk000Sub001Block103Part024

def surrogateDiagonalTailChunk000Sub001Block103Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block103HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block103MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block103TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block103 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block103Part000
    + surrogateDiagTailX0RatChunk000Sub001Block103Part001
    + surrogateDiagTailX0RatChunk000Sub001Block103Part002
    + surrogateDiagTailX0RatChunk000Sub001Block103Part003
    + surrogateDiagTailX0RatChunk000Sub001Block103Part004
    + surrogateDiagTailX0RatChunk000Sub001Block103Part005
    + surrogateDiagTailX0RatChunk000Sub001Block103Part006
    + surrogateDiagTailX0RatChunk000Sub001Block103Part007
    + surrogateDiagTailX0RatChunk000Sub001Block103Part008
    + surrogateDiagTailX0RatChunk000Sub001Block103Part009
    + surrogateDiagTailX0RatChunk000Sub001Block103Part010
    + surrogateDiagTailX0RatChunk000Sub001Block103Part011
    + surrogateDiagTailX0RatChunk000Sub001Block103Part012
    + surrogateDiagTailX0RatChunk000Sub001Block103Part013
    + surrogateDiagTailX0RatChunk000Sub001Block103Part014
    + surrogateDiagTailX0RatChunk000Sub001Block103Part015
    + surrogateDiagTailX0RatChunk000Sub001Block103Part016
    + surrogateDiagTailX0RatChunk000Sub001Block103Part017
    + surrogateDiagTailX0RatChunk000Sub001Block103Part018
    + surrogateDiagTailX0RatChunk000Sub001Block103Part019
    + surrogateDiagTailX0RatChunk000Sub001Block103Part020
    + surrogateDiagTailX0RatChunk000Sub001Block103Part021
    + surrogateDiagTailX0RatChunk000Sub001Block103Part022
    + surrogateDiagTailX0RatChunk000Sub001Block103Part023
    + surrogateDiagTailX0RatChunk000Sub001Block103Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block103_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block103Head + surrogateDiagTailX0RatChunk000Sub001Block103Mid + surrogateDiagTailX0RatChunk000Sub001Block103Tail =
      surrogateDiagTailX0RatChunk000Sub001Block103 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block103Head surrogateDiagTailX0RatChunk000Sub001Block103Mid surrogateDiagTailX0RatChunk000Sub001Block103Tail surrogateDiagTailX0RatChunk000Sub001Block103
  ring

def SurrogateDiagonalTailChunk000Sub001Block103HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block103HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block103Head

def SurrogateDiagonalTailChunk000Sub001Block103MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block103MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block103Mid

def SurrogateDiagonalTailChunk000Sub001Block103TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block103TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block103Tail

theorem surrogateDiagonalTailChunk000Sub001Block103_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block103HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block103MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block103TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block103Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block103 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block103HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block103MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block103TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block103Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block103_eq_head_add_mid_add_tail

/-- Block 104 covers tail-support indices [7600,7625) and q from 12559 to 12598. -/

def TailChunk000Sub001Block104Part000SupportExplicit : Finset ℕ :=
  ([12559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part000 : ℚ :=
  (179817239381 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk000Sub001Block104Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12559
    = surrogateDiagTailX0RatChunk000Sub001Block104Part000

theorem surrogateDiagonalTailChunk000Sub001Block104Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part000] using hcert

def TailChunk000Sub001Block104Part001SupportExplicit : Finset ℕ :=
  ([12561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part001 : ℚ :=
  (1047838962775 : ℚ) / 2706940036656340992

def SurrogateDiagonalTailChunk000Sub001Block104Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12561
    = surrogateDiagTailX0RatChunk000Sub001Block104Part001

theorem surrogateDiagonalTailChunk000Sub001Block104Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part001] using hcert

def TailChunk000Sub001Block104Part002SupportExplicit : Finset ℕ :=
  ([12562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part002 : ℚ :=
  (87864767047 : ℚ) / 105581122002000000

def SurrogateDiagonalTailChunk000Sub001Block104Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12562
    = surrogateDiagTailX0RatChunk000Sub001Block104Part002

theorem surrogateDiagonalTailChunk000Sub001Block104Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part002] using hcert

def TailChunk000Sub001Block104Part003SupportExplicit : Finset ℕ :=
  ([12563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part003 : ℚ :=
  (4462314406175 : ℚ) / 24305370247442202624

def SurrogateDiagonalTailChunk000Sub001Block104Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12563
    = surrogateDiagTailX0RatChunk000Sub001Block104Part003

theorem surrogateDiagonalTailChunk000Sub001Block104Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part003] using hcert

def TailChunk000Sub001Block104Part004SupportExplicit : Finset ℕ :=
  ([12565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part004 : ℚ :=
  (5246573054425 : ℚ) / 13627115355673755648

def SurrogateDiagonalTailChunk000Sub001Block104Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12565
    = surrogateDiagTailX0RatChunk000Sub001Block104Part004

theorem surrogateDiagonalTailChunk000Sub001Block104Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part004] using hcert

def TailChunk000Sub001Block104Part005SupportExplicit : Finset ℕ :=
  ([12566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part005 : ℚ :=
  (1328026039 : ℚ) / 1948767563577600

def SurrogateDiagonalTailChunk000Sub001Block104Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12566
    = surrogateDiagTailX0RatChunk000Sub001Block104Part005

theorem surrogateDiagonalTailChunk000Sub001Block104Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part005] using hcert

def TailChunk000Sub001Block104Part006SupportExplicit : Finset ℕ :=
  ([12567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part006 : ℚ :=
  (55975250031 : ℚ) / 144940485746022400

def SurrogateDiagonalTailChunk000Sub001Block104Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12567
    = surrogateDiagTailX0RatChunk000Sub001Block104Part006

theorem surrogateDiagonalTailChunk000Sub001Block104Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part006] using hcert

def TailChunk000Sub001Block104Part007SupportExplicit : Finset ℕ :=
  ([12569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part007 : ℚ :=
  (2468433765625 : ℚ) / 15596658234768732672

def SurrogateDiagonalTailChunk000Sub001Block104Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12569
    = surrogateDiagTailX0RatChunk000Sub001Block104Part007

theorem surrogateDiagonalTailChunk000Sub001Block104Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part007] using hcert

def TailChunk000Sub001Block104Part008SupportExplicit : Finset ℕ :=
  ([12570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part008 : ℚ :=
  (623825489525 : ℚ) / 156337059180724224

def SurrogateDiagonalTailChunk000Sub001Block104Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12570
    = surrogateDiagTailX0RatChunk000Sub001Block104Part008

theorem surrogateDiagonalTailChunk000Sub001Block104Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part008] using hcert

def TailChunk000Sub001Block104Part009SupportExplicit : Finset ℕ :=
  ([12571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part009 : ℚ :=
  (4318208519825 : ℚ) / 22575134843252941824

def SurrogateDiagonalTailChunk000Sub001Block104Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12571
    = surrogateDiagTailX0RatChunk000Sub001Block104Part009

theorem surrogateDiagonalTailChunk000Sub001Block104Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part009] using hcert

def TailChunk000Sub001Block104Part010SupportExplicit : Finset ℕ :=
  ([12574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part010 : ℚ :=
  (617599515625 : ℚ) / 976032713965301202

def SurrogateDiagonalTailChunk000Sub001Block104Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12574
    = surrogateDiagTailX0RatChunk000Sub001Block104Part010

theorem surrogateDiagonalTailChunk000Sub001Block104Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part010] using hcert

def TailChunk000Sub001Block104Part011SupportExplicit : Finset ℕ :=
  ([12577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part011 : ℚ :=
  (2471577015625 : ℚ) / 15636407582536630272

def SurrogateDiagonalTailChunk000Sub001Block104Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12577
    = surrogateDiagTailX0RatChunk000Sub001Block104Part011

theorem surrogateDiagonalTailChunk000Sub001Block104Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part011] using hcert

def TailChunk000Sub001Block104Part012SupportExplicit : Finset ℕ :=
  ([12578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part012 : ℚ :=
  (4193731687 : ℚ) / 5659915524753600

def SurrogateDiagonalTailChunk000Sub001Block104Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12578
    = surrogateDiagTailX0RatChunk000Sub001Block104Part012

theorem surrogateDiagonalTailChunk000Sub001Block104Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part012] using hcert

def TailChunk000Sub001Block104Part013SupportExplicit : Finset ℕ :=
  ([12579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part013 : ℚ :=
  (1767453226625 : ℚ) / 3315328624689030144

def SurrogateDiagonalTailChunk000Sub001Block104Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12579
    = surrogateDiagTailX0RatChunk000Sub001Block104Part013

theorem surrogateDiagonalTailChunk000Sub001Block104Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part013] using hcert

def TailChunk000Sub001Block104Part014SupportExplicit : Finset ℕ :=
  ([12581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part014 : ℚ :=
  (254861091725 : ℚ) / 1446057799490592288

def SurrogateDiagonalTailChunk000Sub001Block104Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12581
    = surrogateDiagTailX0RatChunk000Sub001Block104Part014

theorem surrogateDiagonalTailChunk000Sub001Block104Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part014] using hcert

def TailChunk000Sub001Block104Part015SupportExplicit : Finset ℕ :=
  ([12583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part015 : ℚ :=
  (2473935765625 : ℚ) / 15666269417115561522

def SurrogateDiagonalTailChunk000Sub001Block104Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12583
    = surrogateDiagTailX0RatChunk000Sub001Block104Part015

theorem surrogateDiagonalTailChunk000Sub001Block104Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part015] using hcert

def TailChunk000Sub001Block104Part016SupportExplicit : Finset ℕ :=
  ([12585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part016 : ℚ :=
  (1054114714575 : ℚ) / 1683610504066072576

def SurrogateDiagonalTailChunk000Sub001Block104Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12585
    = surrogateDiagTailX0RatChunk000Sub001Block104Part016

theorem surrogateDiagonalTailChunk000Sub001Block104Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part016] using hcert

def TailChunk000Sub001Block104Part017SupportExplicit : Finset ℕ :=
  ([12586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part017 : ℚ :=
  (829242781 : ℚ) / 717078145351680

def SurrogateDiagonalTailChunk000Sub001Block104Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12586
    = surrogateDiagTailX0RatChunk000Sub001Block104Part017

theorem surrogateDiagonalTailChunk000Sub001Block104Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part017] using hcert

def TailChunk000Sub001Block104Part018SupportExplicit : Finset ℕ :=
  ([12587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part018 : ℚ :=
  (31549814597 : ℚ) / 187081686103449600

def SurrogateDiagonalTailChunk000Sub001Block104Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12587
    = surrogateDiagTailX0RatChunk000Sub001Block104Part018

theorem surrogateDiagonalTailChunk000Sub001Block104Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part018] using hcert

def TailChunk000Sub001Block104Part019SupportExplicit : Finset ℕ :=
  ([12589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part019 : ℚ :=
  (2476295640625 : ℚ) / 15696174003060156192

def SurrogateDiagonalTailChunk000Sub001Block104Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12589
    = surrogateDiagTailX0RatChunk000Sub001Block104Part019

theorem surrogateDiagonalTailChunk000Sub001Block104Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part019] using hcert

def TailChunk000Sub001Block104Part020SupportExplicit : Finset ℕ :=
  ([12590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part020 : ℚ :=
  (117556311475 : ℚ) / 100200388634352768

def SurrogateDiagonalTailChunk000Sub001Block104Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12590
    = surrogateDiagTailX0RatChunk000Sub001Block104Part020

theorem surrogateDiagonalTailChunk000Sub001Block104Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part020] using hcert

def TailChunk000Sub001Block104Part021SupportExplicit : Finset ℕ :=
  ([12594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part021 : ℚ :=
  (43010819225 : ℚ) / 24222490745463204

def SurrogateDiagonalTailChunk000Sub001Block104Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12594
    = surrogateDiagTailX0RatChunk000Sub001Block104Part021

theorem surrogateDiagonalTailChunk000Sub001Block104Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part021] using hcert

def TailChunk000Sub001Block104Part022SupportExplicit : Finset ℕ :=
  ([12595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part022 : ℚ :=
  (23184757903 : ℚ) / 69193644115230720

def SurrogateDiagonalTailChunk000Sub001Block104Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12595
    = surrogateDiagTailX0RatChunk000Sub001Block104Part022

theorem surrogateDiagonalTailChunk000Sub001Block104Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part022] using hcert

def TailChunk000Sub001Block104Part023SupportExplicit : Finset ℕ :=
  ([12597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part023 : ℚ :=
  (140233461625 : ℚ) / 237810231155884032

def SurrogateDiagonalTailChunk000Sub001Block104Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12597
    = surrogateDiagTailX0RatChunk000Sub001Block104Part023

theorem surrogateDiagonalTailChunk000Sub001Block104Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part023] using hcert

def TailChunk000Sub001Block104Part024SupportExplicit : Finset ℕ :=
  ([12598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block104Part024 : ℚ :=
  (619959390625 : ℚ) / 983507084808554802

def SurrogateDiagonalTailChunk000Sub001Block104Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12598
    = surrogateDiagTailX0RatChunk000Sub001Block104Part024

theorem surrogateDiagonalTailChunk000Sub001Block104Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block104Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block104Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block104Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block104Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block104Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block104HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block104Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block104Part000
    + surrogateDiagTailX0RatChunk000Sub001Block104Part001
    + surrogateDiagTailX0RatChunk000Sub001Block104Part002
    + surrogateDiagTailX0RatChunk000Sub001Block104Part003
    + surrogateDiagTailX0RatChunk000Sub001Block104Part004
    + surrogateDiagTailX0RatChunk000Sub001Block104Part005
    + surrogateDiagTailX0RatChunk000Sub001Block104Part006
    + surrogateDiagTailX0RatChunk000Sub001Block104Part007
    + surrogateDiagTailX0RatChunk000Sub001Block104Part008
    + surrogateDiagTailX0RatChunk000Sub001Block104Part009

def surrogateDiagonalTailChunk000Sub001Block104MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block104Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block104Part010
    + surrogateDiagTailX0RatChunk000Sub001Block104Part011
    + surrogateDiagTailX0RatChunk000Sub001Block104Part012
    + surrogateDiagTailX0RatChunk000Sub001Block104Part013
    + surrogateDiagTailX0RatChunk000Sub001Block104Part014
    + surrogateDiagTailX0RatChunk000Sub001Block104Part015
    + surrogateDiagTailX0RatChunk000Sub001Block104Part016
    + surrogateDiagTailX0RatChunk000Sub001Block104Part017
    + surrogateDiagTailX0RatChunk000Sub001Block104Part018
    + surrogateDiagTailX0RatChunk000Sub001Block104Part019

def surrogateDiagonalTailChunk000Sub001Block104TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block104Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block104Part020
    + surrogateDiagTailX0RatChunk000Sub001Block104Part021
    + surrogateDiagTailX0RatChunk000Sub001Block104Part022
    + surrogateDiagTailX0RatChunk000Sub001Block104Part023
    + surrogateDiagTailX0RatChunk000Sub001Block104Part024

def surrogateDiagonalTailChunk000Sub001Block104Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block104HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block104MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block104TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block104 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block104Part000
    + surrogateDiagTailX0RatChunk000Sub001Block104Part001
    + surrogateDiagTailX0RatChunk000Sub001Block104Part002
    + surrogateDiagTailX0RatChunk000Sub001Block104Part003
    + surrogateDiagTailX0RatChunk000Sub001Block104Part004
    + surrogateDiagTailX0RatChunk000Sub001Block104Part005
    + surrogateDiagTailX0RatChunk000Sub001Block104Part006
    + surrogateDiagTailX0RatChunk000Sub001Block104Part007
    + surrogateDiagTailX0RatChunk000Sub001Block104Part008
    + surrogateDiagTailX0RatChunk000Sub001Block104Part009
    + surrogateDiagTailX0RatChunk000Sub001Block104Part010
    + surrogateDiagTailX0RatChunk000Sub001Block104Part011
    + surrogateDiagTailX0RatChunk000Sub001Block104Part012
    + surrogateDiagTailX0RatChunk000Sub001Block104Part013
    + surrogateDiagTailX0RatChunk000Sub001Block104Part014
    + surrogateDiagTailX0RatChunk000Sub001Block104Part015
    + surrogateDiagTailX0RatChunk000Sub001Block104Part016
    + surrogateDiagTailX0RatChunk000Sub001Block104Part017
    + surrogateDiagTailX0RatChunk000Sub001Block104Part018
    + surrogateDiagTailX0RatChunk000Sub001Block104Part019
    + surrogateDiagTailX0RatChunk000Sub001Block104Part020
    + surrogateDiagTailX0RatChunk000Sub001Block104Part021
    + surrogateDiagTailX0RatChunk000Sub001Block104Part022
    + surrogateDiagTailX0RatChunk000Sub001Block104Part023
    + surrogateDiagTailX0RatChunk000Sub001Block104Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block104_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block104Head + surrogateDiagTailX0RatChunk000Sub001Block104Mid + surrogateDiagTailX0RatChunk000Sub001Block104Tail =
      surrogateDiagTailX0RatChunk000Sub001Block104 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block104Head surrogateDiagTailX0RatChunk000Sub001Block104Mid surrogateDiagTailX0RatChunk000Sub001Block104Tail surrogateDiagTailX0RatChunk000Sub001Block104
  ring

def SurrogateDiagonalTailChunk000Sub001Block104HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block104HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block104Head

def SurrogateDiagonalTailChunk000Sub001Block104MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block104MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block104Mid

def SurrogateDiagonalTailChunk000Sub001Block104TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block104TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block104Tail

theorem surrogateDiagonalTailChunk000Sub001Block104_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block104HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block104MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block104TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block104Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block104 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block104HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block104MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block104TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block104Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block104_eq_head_add_mid_add_tail

/-- Block 105 covers tail-support indices [7625,7650) and q from 12599 to 12639. -/

def TailChunk000Sub001Block105Part000SupportExplicit : Finset ℕ :=
  ([12599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part000 : ℚ :=
  (4749946635425 : ℚ) / 28282997204902831104

def SurrogateDiagonalTailChunk000Sub001Block105Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12599
    = surrogateDiagTailX0RatChunk000Sub001Block105Part000

theorem surrogateDiagonalTailChunk000Sub001Block105Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part000] using hcert

def TailChunk000Sub001Block105Part001SupportExplicit : Finset ℕ :=
  ([12601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part001 : ℚ :=
  (158785201 : ℚ) / 1008391141900800

def SurrogateDiagonalTailChunk000Sub001Block105Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12601
    = surrogateDiagTailX0RatChunk000Sub001Block105Part001

theorem surrogateDiagonalTailChunk000Sub001Block105Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part001] using hcert

def TailChunk000Sub001Block105Part002SupportExplicit : Finset ℕ :=
  ([12602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part002 : ℚ :=
  (39702601 : ℚ) / 63024446368800

def SurrogateDiagonalTailChunk000Sub001Block105Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12602
    = surrogateDiagTailX0RatChunk000Sub001Block105Part002

theorem surrogateDiagonalTailChunk000Sub001Block105Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part002] using hcert

def TailChunk000Sub001Block105Part003SupportExplicit : Finset ℕ :=
  ([12603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part003 : ℚ :=
  (176424983197 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk000Sub001Block105Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12603
    = surrogateDiagTailX0RatChunk000Sub001Block105Part003

theorem surrogateDiagonalTailChunk000Sub001Block105Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part003] using hcert

def TailChunk000Sub001Block105Part004SupportExplicit : Finset ℕ :=
  ([12605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part004 : ℚ :=
  (269967416659 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk000Sub001Block105Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12605
    = surrogateDiagTailX0RatChunk000Sub001Block105Part004

theorem surrogateDiagonalTailChunk000Sub001Block105Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part004] using hcert

def TailChunk000Sub001Block105Part005SupportExplicit : Finset ℕ :=
  ([12606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part005 : ℚ :=
  (1466307943 : ℚ) / 521388256800000

def SurrogateDiagonalTailChunk000Sub001Block105Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12606
    = surrogateDiagTailX0RatChunk000Sub001Block105Part005

theorem surrogateDiagonalTailChunk000Sub001Block105Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part005] using hcert

def TailChunk000Sub001Block105Part006SupportExplicit : Finset ℕ :=
  ([12607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part006 : ℚ :=
  (76977621763 : ℚ) / 340190264448000000

def SurrogateDiagonalTailChunk000Sub001Block105Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12607
    = surrogateDiagTailX0RatChunk000Sub001Block105Part006

theorem surrogateDiagonalTailChunk000Sub001Block105Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part006] using hcert

def TailChunk000Sub001Block105Part007SupportExplicit : Finset ℕ :=
  ([12610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part007 : ℚ :=
  (1705144479625 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub001Block105Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12610
    = surrogateDiagTailX0RatChunk000Sub001Block105Part007

theorem surrogateDiagonalTailChunk000Sub001Block105Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part007] using hcert

def TailChunk000Sub001Block105Part008SupportExplicit : Finset ℕ :=
  ([12611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part008 : ℚ :=
  (3975933025 : ℚ) / 25289904915999282

def SurrogateDiagonalTailChunk000Sub001Block105Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12611
    = surrogateDiagTailX0RatChunk000Sub001Block105Part008

theorem surrogateDiagonalTailChunk000Sub001Block105Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part008] using hcert

def TailChunk000Sub001Block105Part009SupportExplicit : Finset ℕ :=
  ([12613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part009 : ℚ :=
  (2485746390625 : ℚ) / 15816220676457928992

def SurrogateDiagonalTailChunk000Sub001Block105Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12613
    = surrogateDiagTailX0RatChunk000Sub001Block105Part009

theorem surrogateDiagonalTailChunk000Sub001Block105Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part009] using hcert

def TailChunk000Sub001Block105Part010SupportExplicit : Finset ℕ :=
  ([12614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part010 : ℚ :=
  (1895430372625 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub001Block105Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12614
    = surrogateDiagTailX0RatChunk000Sub001Block105Part010

theorem surrogateDiagonalTailChunk000Sub001Block105Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part010] using hcert

def TailChunk000Sub001Block105Part011SupportExplicit : Finset ℕ :=
  ([12617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part011 : ℚ :=
  (77653651201 : ℚ) / 340190264448000000

def SurrogateDiagonalTailChunk000Sub001Block105Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12617
    = surrogateDiagTailX0RatChunk000Sub001Block105Part011

theorem surrogateDiagonalTailChunk000Sub001Block105Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part011] using hcert

def TailChunk000Sub001Block105Part012SupportExplicit : Finset ℕ :=
  ([12619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part012 : ℚ :=
  (2488111890625 : ℚ) / 15846339631373044722

def SurrogateDiagonalTailChunk000Sub001Block105Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12619
    = surrogateDiagTailX0RatChunk000Sub001Block105Part012

theorem surrogateDiagonalTailChunk000Sub001Block105Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part012] using hcert

def TailChunk000Sub001Block105Part013SupportExplicit : Finset ℕ :=
  ([12621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part013 : ℚ :=
  (17387539297 : ℚ) / 26879230771200000

def SurrogateDiagonalTailChunk000Sub001Block105Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12621
    = surrogateDiagTailX0RatChunk000Sub001Block105Part013

theorem surrogateDiagonalTailChunk000Sub001Block105Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part013] using hcert

def TailChunk000Sub001Block105Part014SupportExplicit : Finset ℕ :=
  ([12622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part014 : ℚ :=
  (995718025 : ℚ) / 1585638883573842

def SurrogateDiagonalTailChunk000Sub001Block105Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12622
    = surrogateDiagTailX0RatChunk000Sub001Block105Part014

theorem surrogateDiagonalTailChunk000Sub001Block105Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part014] using hcert

def TailChunk000Sub001Block105Part015SupportExplicit : Finset ℕ :=
  ([12623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part015 : ℚ :=
  (350682072079 : ℚ) / 1836110319450163200

def SurrogateDiagonalTailChunk000Sub001Block105Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12623
    = surrogateDiagTailX0RatChunk000Sub001Block105Part015

theorem surrogateDiagonalTailChunk000Sub001Block105Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part015] using hcert

def TailChunk000Sub001Block105Part016SupportExplicit : Finset ℕ :=
  ([12626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part016 : ℚ :=
  (8478941775 : ℚ) / 595403034626072768

def SurrogateDiagonalTailChunk000Sub001Block105Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12626
    = surrogateDiagTailX0RatChunk000Sub001Block105Part016

theorem surrogateDiagonalTailChunk000Sub001Block105Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part016] using hcert

def TailChunk000Sub001Block105Part017SupportExplicit : Finset ℕ :=
  ([12629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part017 : ℚ :=
  (6305390575 : ℚ) / 4901052855456497664

def SurrogateDiagonalTailChunk000Sub001Block105Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12629
    = surrogateDiagTailX0RatChunk000Sub001Block105Part017

theorem surrogateDiagonalTailChunk000Sub001Block105Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part017] using hcert

def TailChunk000Sub001Block105Part018SupportExplicit : Finset ℕ :=
  ([12630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part018 : ℚ :=
  (442774681 : ℚ) / 236075109580800

def SurrogateDiagonalTailChunk000Sub001Block105Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12630
    = surrogateDiagTailX0RatChunk000Sub001Block105Part018

theorem surrogateDiagonalTailChunk000Sub001Block105Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part018] using hcert

def TailChunk000Sub001Block105Part019SupportExplicit : Finset ℕ :=
  ([12631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part019 : ℚ :=
  (17541495275 : ℚ) / 3548087936609943552

def SurrogateDiagonalTailChunk000Sub001Block105Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12631
    = surrogateDiagTailX0RatChunk000Sub001Block105Part019

theorem surrogateDiagonalTailChunk000Sub001Block105Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part019] using hcert

def TailChunk000Sub001Block105Part020SupportExplicit : Finset ℕ :=
  ([12633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part020 : ℚ :=
  (4433525329 : ℚ) / 50273047928665920

def SurrogateDiagonalTailChunk000Sub001Block105Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12633
    = surrogateDiagTailX0RatChunk000Sub001Block105Part020

theorem surrogateDiagonalTailChunk000Sub001Block105Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part020] using hcert

def TailChunk000Sub001Block105Part021SupportExplicit : Finset ℕ :=
  ([12634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block105Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12634
    = surrogateDiagTailX0RatChunk000Sub001Block105Part021

theorem surrogateDiagonalTailChunk000Sub001Block105Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part021] using hcert

def TailChunk000Sub001Block105Part022SupportExplicit : Finset ℕ :=
  ([12637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block105Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12637
    = surrogateDiagTailX0RatChunk000Sub001Block105Part022

theorem surrogateDiagonalTailChunk000Sub001Block105Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part022] using hcert

def TailChunk000Sub001Block105Part023SupportExplicit : Finset ℕ :=
  ([12638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part023 : ℚ :=
  (1960888759 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub001Block105Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12638
    = surrogateDiagTailX0RatChunk000Sub001Block105Part023

theorem surrogateDiagonalTailChunk000Sub001Block105Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part023] using hcert

def TailChunk000Sub001Block105Part024SupportExplicit : Finset ℕ :=
  ([12639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block105Part024 : ℚ :=
  (45488328181 : ℚ) / 340769160620083200

def SurrogateDiagonalTailChunk000Sub001Block105Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12639
    = surrogateDiagTailX0RatChunk000Sub001Block105Part024

theorem surrogateDiagonalTailChunk000Sub001Block105Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block105Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block105Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block105Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block105Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block105Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block105HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block105Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block105Part000
    + surrogateDiagTailX0RatChunk000Sub001Block105Part001
    + surrogateDiagTailX0RatChunk000Sub001Block105Part002
    + surrogateDiagTailX0RatChunk000Sub001Block105Part003
    + surrogateDiagTailX0RatChunk000Sub001Block105Part004
    + surrogateDiagTailX0RatChunk000Sub001Block105Part005
    + surrogateDiagTailX0RatChunk000Sub001Block105Part006
    + surrogateDiagTailX0RatChunk000Sub001Block105Part007
    + surrogateDiagTailX0RatChunk000Sub001Block105Part008
    + surrogateDiagTailX0RatChunk000Sub001Block105Part009

def surrogateDiagonalTailChunk000Sub001Block105MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block105Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block105Part010
    + surrogateDiagTailX0RatChunk000Sub001Block105Part011
    + surrogateDiagTailX0RatChunk000Sub001Block105Part012
    + surrogateDiagTailX0RatChunk000Sub001Block105Part013
    + surrogateDiagTailX0RatChunk000Sub001Block105Part014
    + surrogateDiagTailX0RatChunk000Sub001Block105Part015
    + surrogateDiagTailX0RatChunk000Sub001Block105Part016
    + surrogateDiagTailX0RatChunk000Sub001Block105Part017
    + surrogateDiagTailX0RatChunk000Sub001Block105Part018
    + surrogateDiagTailX0RatChunk000Sub001Block105Part019

def surrogateDiagonalTailChunk000Sub001Block105TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block105Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block105Part020
    + surrogateDiagTailX0RatChunk000Sub001Block105Part021
    + surrogateDiagTailX0RatChunk000Sub001Block105Part022
    + surrogateDiagTailX0RatChunk000Sub001Block105Part023
    + surrogateDiagTailX0RatChunk000Sub001Block105Part024

def surrogateDiagonalTailChunk000Sub001Block105Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block105HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block105MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block105TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block105 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block105Part000
    + surrogateDiagTailX0RatChunk000Sub001Block105Part001
    + surrogateDiagTailX0RatChunk000Sub001Block105Part002
    + surrogateDiagTailX0RatChunk000Sub001Block105Part003
    + surrogateDiagTailX0RatChunk000Sub001Block105Part004
    + surrogateDiagTailX0RatChunk000Sub001Block105Part005
    + surrogateDiagTailX0RatChunk000Sub001Block105Part006
    + surrogateDiagTailX0RatChunk000Sub001Block105Part007
    + surrogateDiagTailX0RatChunk000Sub001Block105Part008
    + surrogateDiagTailX0RatChunk000Sub001Block105Part009
    + surrogateDiagTailX0RatChunk000Sub001Block105Part010
    + surrogateDiagTailX0RatChunk000Sub001Block105Part011
    + surrogateDiagTailX0RatChunk000Sub001Block105Part012
    + surrogateDiagTailX0RatChunk000Sub001Block105Part013
    + surrogateDiagTailX0RatChunk000Sub001Block105Part014
    + surrogateDiagTailX0RatChunk000Sub001Block105Part015
    + surrogateDiagTailX0RatChunk000Sub001Block105Part016
    + surrogateDiagTailX0RatChunk000Sub001Block105Part017
    + surrogateDiagTailX0RatChunk000Sub001Block105Part018
    + surrogateDiagTailX0RatChunk000Sub001Block105Part019
    + surrogateDiagTailX0RatChunk000Sub001Block105Part020
    + surrogateDiagTailX0RatChunk000Sub001Block105Part021
    + surrogateDiagTailX0RatChunk000Sub001Block105Part022
    + surrogateDiagTailX0RatChunk000Sub001Block105Part023
    + surrogateDiagTailX0RatChunk000Sub001Block105Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block105_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block105Head + surrogateDiagTailX0RatChunk000Sub001Block105Mid + surrogateDiagTailX0RatChunk000Sub001Block105Tail =
      surrogateDiagTailX0RatChunk000Sub001Block105 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block105Head surrogateDiagTailX0RatChunk000Sub001Block105Mid surrogateDiagTailX0RatChunk000Sub001Block105Tail surrogateDiagTailX0RatChunk000Sub001Block105
  ring

def SurrogateDiagonalTailChunk000Sub001Block105HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block105HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block105Head

def SurrogateDiagonalTailChunk000Sub001Block105MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block105MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block105Mid

def SurrogateDiagonalTailChunk000Sub001Block105TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block105TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block105Tail

theorem surrogateDiagonalTailChunk000Sub001Block105_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block105HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block105MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block105TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block105Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block105 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block105HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block105MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block105TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block105Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block105_eq_head_add_mid_add_tail

/-- Block 106 covers tail-support indices [7650,7675) and q from 12641 to 12682. -/

def TailChunk000Sub001Block106Part000SupportExplicit : Finset ℕ :=
  ([12641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block106Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12641
    = surrogateDiagTailX0RatChunk000Sub001Block106Part000

theorem surrogateDiagonalTailChunk000Sub001Block106Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part000] using hcert

def TailChunk000Sub001Block106Part001SupportExplicit : Finset ℕ :=
  ([12643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part001 : ℚ :=
  (49655033525 : ℚ) / 28878016889504523264

def SurrogateDiagonalTailChunk000Sub001Block106Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12643
    = surrogateDiagTailX0RatChunk000Sub001Block106Part001

theorem surrogateDiagonalTailChunk000Sub001Block106Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part001] using hcert

def TailChunk000Sub001Block106Part002SupportExplicit : Finset ℕ :=
  ([12646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block106Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12646
    = surrogateDiagTailX0RatChunk000Sub001Block106Part002

theorem surrogateDiagonalTailChunk000Sub001Block106Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part002] using hcert

def TailChunk000Sub001Block106Part003SupportExplicit : Finset ℕ :=
  ([12647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block106Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12647
    = surrogateDiagTailX0RatChunk000Sub001Block106Part003

theorem surrogateDiagonalTailChunk000Sub001Block106Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part003] using hcert

def TailChunk000Sub001Block106Part004SupportExplicit : Finset ℕ :=
  ([12649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part004 : ℚ :=
  (10192250275 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub001Block106Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12649
    = surrogateDiagTailX0RatChunk000Sub001Block106Part004

theorem surrogateDiagonalTailChunk000Sub001Block106Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part004] using hcert

def TailChunk000Sub001Block106Part005SupportExplicit : Finset ℕ :=
  ([12651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part005 : ℚ :=
  (277885270525 : ℚ) / 3160015835975196672

def SurrogateDiagonalTailChunk000Sub001Block106Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12651
    = surrogateDiagTailX0RatChunk000Sub001Block106Part005

theorem surrogateDiagonalTailChunk000Sub001Block106Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part005] using hcert

def TailChunk000Sub001Block106Part006SupportExplicit : Finset ℕ :=
  ([12653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block106Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12653
    = surrogateDiagTailX0RatChunk000Sub001Block106Part006

theorem surrogateDiagonalTailChunk000Sub001Block106Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part006] using hcert

def TailChunk000Sub001Block106Part007SupportExplicit : Finset ℕ :=
  ([12655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part007 : ℚ :=
  (32048113729 : ℚ) / 1049080706922547200

def SurrogateDiagonalTailChunk000Sub001Block106Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12655
    = surrogateDiagTailX0RatChunk000Sub001Block106Part007

theorem surrogateDiagonalTailChunk000Sub001Block106Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part007] using hcert

def TailChunk000Sub001Block106Part008SupportExplicit : Finset ℕ :=
  ([12657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part008 : ℚ :=
  (556297666025 : ℚ) / 6332032678156490304

def SurrogateDiagonalTailChunk000Sub001Block106Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12657
    = surrogateDiagTailX0RatChunk000Sub001Block106Part008

theorem surrogateDiagonalTailChunk000Sub001Block106Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part008] using hcert

def TailChunk000Sub001Block106Part009SupportExplicit : Finset ℕ :=
  ([12658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block106Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12658
    = surrogateDiagTailX0RatChunk000Sub001Block106Part009

theorem surrogateDiagonalTailChunk000Sub001Block106Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part009] using hcert

def TailChunk000Sub001Block106Part010SupportExplicit : Finset ℕ :=
  ([12659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block106Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12659
    = surrogateDiagTailX0RatChunk000Sub001Block106Part010

theorem surrogateDiagonalTailChunk000Sub001Block106Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part010] using hcert

def TailChunk000Sub001Block106Part011SupportExplicit : Finset ℕ :=
  ([12661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part011 : ℚ :=
  (4447386063 : ℚ) / 583118683750000000

def SurrogateDiagonalTailChunk000Sub001Block106Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12661
    = surrogateDiagTailX0RatChunk000Sub001Block106Part011

theorem surrogateDiagonalTailChunk000Sub001Block106Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part011] using hcert

def TailChunk000Sub001Block106Part012SupportExplicit : Finset ℕ :=
  ([12662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part012 : ℚ :=
  (2262794125525 : ℚ) / 2892656869256153088

def SurrogateDiagonalTailChunk000Sub001Block106Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12662
    = surrogateDiagTailX0RatChunk000Sub001Block106Part012

theorem surrogateDiagonalTailChunk000Sub001Block106Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part012] using hcert

def TailChunk000Sub001Block106Part013SupportExplicit : Finset ℕ :=
  ([12665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part013 : ℚ :=
  (887874060925 : ℚ) / 20127675236197859328

def SurrogateDiagonalTailChunk000Sub001Block106Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12665
    = surrogateDiagTailX0RatChunk000Sub001Block106Part013

theorem surrogateDiagonalTailChunk000Sub001Block106Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part013] using hcert

def TailChunk000Sub001Block106Part014SupportExplicit : Finset ℕ :=
  ([12666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part014 : ℚ :=
  (6680649 : ℚ) / 3171391105600

def SurrogateDiagonalTailChunk000Sub001Block106Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12666
    = surrogateDiagTailX0RatChunk000Sub001Block106Part014

theorem surrogateDiagonalTailChunk000Sub001Block106Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part014] using hcert

def TailChunk000Sub001Block106Part015SupportExplicit : Finset ℕ :=
  ([12667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part015 : ℚ :=
  (86893125625 : ℚ) / 58660810829256050688

def SurrogateDiagonalTailChunk000Sub001Block106Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12667
    = surrogateDiagTailX0RatChunk000Sub001Block106Part015

theorem surrogateDiagonalTailChunk000Sub001Block106Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part015] using hcert

def TailChunk000Sub001Block106Part016SupportExplicit : Finset ℕ :=
  ([12669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part016 : ℚ :=
  (22537776791 : ℚ) / 221726442789273600

def SurrogateDiagonalTailChunk000Sub001Block106Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12669
    = surrogateDiagTailX0RatChunk000Sub001Block106Part016

theorem surrogateDiagonalTailChunk000Sub001Block106Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part016] using hcert

def TailChunk000Sub001Block106Part017SupportExplicit : Finset ℕ :=
  ([12670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part017 : ℚ :=
  (63733582447 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block106Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12670
    = surrogateDiagTailX0RatChunk000Sub001Block106Part017

theorem surrogateDiagonalTailChunk000Sub001Block106Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part017] using hcert

def TailChunk000Sub001Block106Part018SupportExplicit : Finset ℕ :=
  ([12671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block106Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12671
    = surrogateDiagTailX0RatChunk000Sub001Block106Part018

theorem surrogateDiagonalTailChunk000Sub001Block106Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part018] using hcert

def TailChunk000Sub001Block106Part019SupportExplicit : Finset ℕ :=
  ([12673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part019 : ℚ :=
  (76494179375 : ℚ) / 6299244675656368128

def SurrogateDiagonalTailChunk000Sub001Block106Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12673
    = surrogateDiagTailX0RatChunk000Sub001Block106Part019

theorem surrogateDiagonalTailChunk000Sub001Block106Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part019] using hcert

def TailChunk000Sub001Block106Part020SupportExplicit : Finset ℕ :=
  ([12674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part020 : ℚ :=
  (627462015625 : ℚ) / 1007459373366116352

def SurrogateDiagonalTailChunk000Sub001Block106Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12674
    = surrogateDiagTailX0RatChunk000Sub001Block106Part020

theorem surrogateDiagonalTailChunk000Sub001Block106Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part020] using hcert

def TailChunk000Sub001Block106Part021SupportExplicit : Finset ℕ :=
  ([12677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part021 : ℚ :=
  (8226107507 : ℚ) / 695626559900481600

def SurrogateDiagonalTailChunk000Sub001Block106Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12677
    = surrogateDiagTailX0RatChunk000Sub001Block106Part021

theorem surrogateDiagonalTailChunk000Sub001Block106Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part021] using hcert

def TailChunk000Sub001Block106Part022SupportExplicit : Finset ℕ :=
  ([12678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part022 : ℚ :=
  (697383955925 : ℚ) / 398008641329823744

def SurrogateDiagonalTailChunk000Sub001Block106Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12678
    = surrogateDiagTailX0RatChunk000Sub001Block106Part022

theorem surrogateDiagonalTailChunk000Sub001Block106Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part022] using hcert

def TailChunk000Sub001Block106Part023SupportExplicit : Finset ℕ :=
  ([12679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part023 : ℚ :=
  (2678659223 : ℚ) / 1122490116620697600

def SurrogateDiagonalTailChunk000Sub001Block106Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12679
    = surrogateDiagTailX0RatChunk000Sub001Block106Part023

theorem surrogateDiagonalTailChunk000Sub001Block106Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part023] using hcert

def TailChunk000Sub001Block106Part024SupportExplicit : Finset ℕ :=
  ([12682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block106Part024 : ℚ :=
  (2323350082375 : ℚ) / 3138185049258590208

def SurrogateDiagonalTailChunk000Sub001Block106Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12682
    = surrogateDiagTailX0RatChunk000Sub001Block106Part024

theorem surrogateDiagonalTailChunk000Sub001Block106Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block106Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block106Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block106Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block106Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block106Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block106HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block106Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block106Part000
    + surrogateDiagTailX0RatChunk000Sub001Block106Part001
    + surrogateDiagTailX0RatChunk000Sub001Block106Part002
    + surrogateDiagTailX0RatChunk000Sub001Block106Part003
    + surrogateDiagTailX0RatChunk000Sub001Block106Part004
    + surrogateDiagTailX0RatChunk000Sub001Block106Part005
    + surrogateDiagTailX0RatChunk000Sub001Block106Part006
    + surrogateDiagTailX0RatChunk000Sub001Block106Part007
    + surrogateDiagTailX0RatChunk000Sub001Block106Part008
    + surrogateDiagTailX0RatChunk000Sub001Block106Part009

def surrogateDiagonalTailChunk000Sub001Block106MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block106Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block106Part010
    + surrogateDiagTailX0RatChunk000Sub001Block106Part011
    + surrogateDiagTailX0RatChunk000Sub001Block106Part012
    + surrogateDiagTailX0RatChunk000Sub001Block106Part013
    + surrogateDiagTailX0RatChunk000Sub001Block106Part014
    + surrogateDiagTailX0RatChunk000Sub001Block106Part015
    + surrogateDiagTailX0RatChunk000Sub001Block106Part016
    + surrogateDiagTailX0RatChunk000Sub001Block106Part017
    + surrogateDiagTailX0RatChunk000Sub001Block106Part018
    + surrogateDiagTailX0RatChunk000Sub001Block106Part019

def surrogateDiagonalTailChunk000Sub001Block106TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block106Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block106Part020
    + surrogateDiagTailX0RatChunk000Sub001Block106Part021
    + surrogateDiagTailX0RatChunk000Sub001Block106Part022
    + surrogateDiagTailX0RatChunk000Sub001Block106Part023
    + surrogateDiagTailX0RatChunk000Sub001Block106Part024

def surrogateDiagonalTailChunk000Sub001Block106Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block106HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block106MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block106TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block106 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block106Part000
    + surrogateDiagTailX0RatChunk000Sub001Block106Part001
    + surrogateDiagTailX0RatChunk000Sub001Block106Part002
    + surrogateDiagTailX0RatChunk000Sub001Block106Part003
    + surrogateDiagTailX0RatChunk000Sub001Block106Part004
    + surrogateDiagTailX0RatChunk000Sub001Block106Part005
    + surrogateDiagTailX0RatChunk000Sub001Block106Part006
    + surrogateDiagTailX0RatChunk000Sub001Block106Part007
    + surrogateDiagTailX0RatChunk000Sub001Block106Part008
    + surrogateDiagTailX0RatChunk000Sub001Block106Part009
    + surrogateDiagTailX0RatChunk000Sub001Block106Part010
    + surrogateDiagTailX0RatChunk000Sub001Block106Part011
    + surrogateDiagTailX0RatChunk000Sub001Block106Part012
    + surrogateDiagTailX0RatChunk000Sub001Block106Part013
    + surrogateDiagTailX0RatChunk000Sub001Block106Part014
    + surrogateDiagTailX0RatChunk000Sub001Block106Part015
    + surrogateDiagTailX0RatChunk000Sub001Block106Part016
    + surrogateDiagTailX0RatChunk000Sub001Block106Part017
    + surrogateDiagTailX0RatChunk000Sub001Block106Part018
    + surrogateDiagTailX0RatChunk000Sub001Block106Part019
    + surrogateDiagTailX0RatChunk000Sub001Block106Part020
    + surrogateDiagTailX0RatChunk000Sub001Block106Part021
    + surrogateDiagTailX0RatChunk000Sub001Block106Part022
    + surrogateDiagTailX0RatChunk000Sub001Block106Part023
    + surrogateDiagTailX0RatChunk000Sub001Block106Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block106_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block106Head + surrogateDiagTailX0RatChunk000Sub001Block106Mid + surrogateDiagTailX0RatChunk000Sub001Block106Tail =
      surrogateDiagTailX0RatChunk000Sub001Block106 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block106Head surrogateDiagTailX0RatChunk000Sub001Block106Mid surrogateDiagTailX0RatChunk000Sub001Block106Tail surrogateDiagTailX0RatChunk000Sub001Block106
  ring

def SurrogateDiagonalTailChunk000Sub001Block106HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block106HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block106Head

def SurrogateDiagonalTailChunk000Sub001Block106MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block106MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block106Mid

def SurrogateDiagonalTailChunk000Sub001Block106TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block106TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block106Tail

theorem surrogateDiagonalTailChunk000Sub001Block106_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block106HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block106MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block106TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block106Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block106 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block106HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block106MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block106TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block106Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block106_eq_head_add_mid_add_tail

/-- Block 107 covers tail-support indices [7675,7700) and q from 12683 to 12722. -/

def TailChunk000Sub001Block107Part000SupportExplicit : Finset ℕ :=
  ([12683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part000 : ℚ :=
  (13388170501 : ℚ) / 1761557267821363200

def SurrogateDiagonalTailChunk000Sub001Block107Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12683
    = surrogateDiagTailX0RatChunk000Sub001Block107Part000

theorem surrogateDiagonalTailChunk000Sub001Block107Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part000] using hcert

def TailChunk000Sub001Block107Part001SupportExplicit : Finset ℕ :=
  ([12685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part001 : ℚ :=
  (216151236325 : ℚ) / 5635286085805350912

def SurrogateDiagonalTailChunk000Sub001Block107Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12685
    = surrogateDiagTailX0RatChunk000Sub001Block107Part001

theorem surrogateDiagonalTailChunk000Sub001Block107Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part001] using hcert

def TailChunk000Sub001Block107Part002SupportExplicit : Finset ℕ :=
  ([12686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part002 : ℚ :=
  (628650765625 : ℚ) / 1011280931423946162

def SurrogateDiagonalTailChunk000Sub001Block107Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12686
    = surrogateDiagTailX0RatChunk000Sub001Block107Part002

theorem surrogateDiagonalTailChunk000Sub001Block107Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part002] using hcert

def TailChunk000Sub001Block107Part003SupportExplicit : Finset ℕ :=
  ([12687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part003 : ℚ :=
  (19962037175 : ℚ) / 228296224377892608

def SurrogateDiagonalTailChunk000Sub001Block107Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12687
    = surrogateDiagTailX0RatChunk000Sub001Block107Part003

theorem surrogateDiagonalTailChunk000Sub001Block107Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part003] using hcert

def TailChunk000Sub001Block107Part004SupportExplicit : Finset ℕ :=
  ([12689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block107Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12689
    = surrogateDiagTailX0RatChunk000Sub001Block107Part004

theorem surrogateDiagonalTailChunk000Sub001Block107Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part004] using hcert

def TailChunk000Sub001Block107Part005SupportExplicit : Finset ℕ :=
  ([12693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part005 : ℚ :=
  (4475725327 : ℚ) / 51235184253453120

def SurrogateDiagonalTailChunk000Sub001Block107Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12693
    = surrogateDiagTailX0RatChunk000Sub001Block107Part005

theorem surrogateDiagonalTailChunk000Sub001Block107Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part005] using hcert

def TailChunk000Sub001Block107Part006SupportExplicit : Finset ℕ :=
  ([12694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part006 : ℚ :=
  (89721644623 : ℚ) / 110097329238835200

def SurrogateDiagonalTailChunk000Sub001Block107Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12694
    = surrogateDiagTailX0RatChunk000Sub001Block107Part006

theorem surrogateDiagonalTailChunk000Sub001Block107Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part006] using hcert

def TailChunk000Sub001Block107Part007SupportExplicit : Finset ℕ :=
  ([12695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part007 : ℚ :=
  (5718225725 : ℚ) / 188371060404185088

def SurrogateDiagonalTailChunk000Sub001Block107Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12695
    = surrogateDiagTailX0RatChunk000Sub001Block107Part007

theorem surrogateDiagonalTailChunk000Sub001Block107Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part007] using hcert

def TailChunk000Sub001Block107Part008SupportExplicit : Finset ℕ :=
  ([12697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block107Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12697
    = surrogateDiagTailX0RatChunk000Sub001Block107Part008

theorem surrogateDiagonalTailChunk000Sub001Block107Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part008] using hcert

def TailChunk000Sub001Block107Part009SupportExplicit : Finset ℕ :=
  ([12698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part009 : ℚ :=
  (2054331461275 : ℚ) / 2183457038109844608

def SurrogateDiagonalTailChunk000Sub001Block107Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12698
    = surrogateDiagTailX0RatChunk000Sub001Block107Part009

theorem surrogateDiagonalTailChunk000Sub001Block107Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part009] using hcert

def TailChunk000Sub001Block107Part010SupportExplicit : Finset ℕ :=
  ([12701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part010 : ℚ :=
  (301194695125 : ℚ) / 47049077628566765568

def SurrogateDiagonalTailChunk000Sub001Block107Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12701
    = surrogateDiagTailX0RatChunk000Sub001Block107Part010

theorem surrogateDiagonalTailChunk000Sub001Block107Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part010] using hcert

def TailChunk000Sub001Block107Part011SupportExplicit : Finset ℕ :=
  ([12702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part011 : ℚ :=
  (443077921975 : ℚ) / 220286406252036096

def SurrogateDiagonalTailChunk000Sub001Block107Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12702
    = surrogateDiagTailX0RatChunk000Sub001Block107Part011

theorem surrogateDiagonalTailChunk000Sub001Block107Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part011] using hcert

def TailChunk000Sub001Block107Part012SupportExplicit : Finset ℕ :=
  ([12703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block107Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12703
    = surrogateDiagTailX0RatChunk000Sub001Block107Part012

theorem surrogateDiagonalTailChunk000Sub001Block107Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part012] using hcert

def TailChunk000Sub001Block107Part013SupportExplicit : Finset ℕ :=
  ([12706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part013 : ℚ :=
  (630634515625 : ℚ) / 1017674342415409152

def SurrogateDiagonalTailChunk000Sub001Block107Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12706
    = surrogateDiagTailX0RatChunk000Sub001Block107Part013

theorem surrogateDiagonalTailChunk000Sub001Block107Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part013] using hcert

def TailChunk000Sub001Block107Part014SupportExplicit : Finset ℕ :=
  ([12707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part014 : ℚ :=
  (2803815451 : ℚ) / 2426303873758003200

def SurrogateDiagonalTailChunk000Sub001Block107Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12707
    = surrogateDiagTailX0RatChunk000Sub001Block107Part014

theorem surrogateDiagonalTailChunk000Sub001Block107Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part014] using hcert

def TailChunk000Sub001Block107Part015SupportExplicit : Finset ℕ :=
  ([12709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part015 : ℚ :=
  (439407121 : ℚ) / 344398284491721600

def SurrogateDiagonalTailChunk000Sub001Block107Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12709
    = surrogateDiagTailX0RatChunk000Sub001Block107Part015

theorem surrogateDiagonalTailChunk000Sub001Block107Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part015] using hcert

def TailChunk000Sub001Block107Part016SupportExplicit : Finset ℕ :=
  ([12710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part016 : ℚ :=
  (11957679809 : ℚ) / 8849129472000000

def SurrogateDiagonalTailChunk000Sub001Block107Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12710
    = surrogateDiagTailX0RatChunk000Sub001Block107Part016

theorem surrogateDiagonalTailChunk000Sub001Block107Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part016] using hcert

def TailChunk000Sub001Block107Part017SupportExplicit : Finset ℕ :=
  ([12711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part017 : ℚ :=
  (3846746525 : ℚ) / 34463314930169088

def SurrogateDiagonalTailChunk000Sub001Block107Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12711
    = surrogateDiagTailX0RatChunk000Sub001Block107Part017

theorem surrogateDiagonalTailChunk000Sub001Block107Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part017] using hcert

def TailChunk000Sub001Block107Part018SupportExplicit : Finset ℕ :=
  ([12713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block107Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12713
    = surrogateDiagTailX0RatChunk000Sub001Block107Part018

theorem surrogateDiagonalTailChunk000Sub001Block107Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part018] using hcert

def TailChunk000Sub001Block107Part019SupportExplicit : Finset ℕ :=
  ([12714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part019 : ℚ :=
  (1515132953875 : ℚ) / 571389011211091968

def SurrogateDiagonalTailChunk000Sub001Block107Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12714
    = surrogateDiagTailX0RatChunk000Sub001Block107Part019

theorem surrogateDiagonalTailChunk000Sub001Block107Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part019] using hcert

def TailChunk000Sub001Block107Part020SupportExplicit : Finset ℕ :=
  ([12715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part020 : ℚ :=
  (808809318025 : ℚ) / 26728156717116377088

def SurrogateDiagonalTailChunk000Sub001Block107Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12715
    = surrogateDiagTailX0RatChunk000Sub001Block107Part020

theorem surrogateDiagonalTailChunk000Sub001Block107Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part020] using hcert

def TailChunk000Sub001Block107Part021SupportExplicit : Finset ℕ :=
  ([12718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part021 : ℚ :=
  (631826265625 : ℚ) / 1021524911066197362

def SurrogateDiagonalTailChunk000Sub001Block107Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12718
    = surrogateDiagTailX0RatChunk000Sub001Block107Part021

theorem surrogateDiagonalTailChunk000Sub001Block107Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part021] using hcert

def TailChunk000Sub001Block107Part022SupportExplicit : Finset ℕ :=
  ([12719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part022 : ℚ :=
  (138023911375 : ℚ) / 7024913858083410432

def SurrogateDiagonalTailChunk000Sub001Block107Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12719
    = surrogateDiagTailX0RatChunk000Sub001Block107Part022

theorem surrogateDiagonalTailChunk000Sub001Block107Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part022] using hcert

def TailChunk000Sub001Block107Part023SupportExplicit : Finset ℕ :=
  ([12721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block107Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12721
    = surrogateDiagTailX0RatChunk000Sub001Block107Part023

theorem surrogateDiagonalTailChunk000Sub001Block107Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part023] using hcert

def TailChunk000Sub001Block107Part024SupportExplicit : Finset ℕ :=
  ([12722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block107Part024 : ℚ :=
  (1011558025 : ℚ) / 1636497374188032

def SurrogateDiagonalTailChunk000Sub001Block107Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12722
    = surrogateDiagTailX0RatChunk000Sub001Block107Part024

theorem surrogateDiagonalTailChunk000Sub001Block107Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block107Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block107Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block107Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block107Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block107Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block107HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block107Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block107Part000
    + surrogateDiagTailX0RatChunk000Sub001Block107Part001
    + surrogateDiagTailX0RatChunk000Sub001Block107Part002
    + surrogateDiagTailX0RatChunk000Sub001Block107Part003
    + surrogateDiagTailX0RatChunk000Sub001Block107Part004
    + surrogateDiagTailX0RatChunk000Sub001Block107Part005
    + surrogateDiagTailX0RatChunk000Sub001Block107Part006
    + surrogateDiagTailX0RatChunk000Sub001Block107Part007
    + surrogateDiagTailX0RatChunk000Sub001Block107Part008
    + surrogateDiagTailX0RatChunk000Sub001Block107Part009

def surrogateDiagonalTailChunk000Sub001Block107MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block107Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block107Part010
    + surrogateDiagTailX0RatChunk000Sub001Block107Part011
    + surrogateDiagTailX0RatChunk000Sub001Block107Part012
    + surrogateDiagTailX0RatChunk000Sub001Block107Part013
    + surrogateDiagTailX0RatChunk000Sub001Block107Part014
    + surrogateDiagTailX0RatChunk000Sub001Block107Part015
    + surrogateDiagTailX0RatChunk000Sub001Block107Part016
    + surrogateDiagTailX0RatChunk000Sub001Block107Part017
    + surrogateDiagTailX0RatChunk000Sub001Block107Part018
    + surrogateDiagTailX0RatChunk000Sub001Block107Part019

def surrogateDiagonalTailChunk000Sub001Block107TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block107Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block107Part020
    + surrogateDiagTailX0RatChunk000Sub001Block107Part021
    + surrogateDiagTailX0RatChunk000Sub001Block107Part022
    + surrogateDiagTailX0RatChunk000Sub001Block107Part023
    + surrogateDiagTailX0RatChunk000Sub001Block107Part024

def surrogateDiagonalTailChunk000Sub001Block107Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block107HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block107MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block107TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block107 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block107Part000
    + surrogateDiagTailX0RatChunk000Sub001Block107Part001
    + surrogateDiagTailX0RatChunk000Sub001Block107Part002
    + surrogateDiagTailX0RatChunk000Sub001Block107Part003
    + surrogateDiagTailX0RatChunk000Sub001Block107Part004
    + surrogateDiagTailX0RatChunk000Sub001Block107Part005
    + surrogateDiagTailX0RatChunk000Sub001Block107Part006
    + surrogateDiagTailX0RatChunk000Sub001Block107Part007
    + surrogateDiagTailX0RatChunk000Sub001Block107Part008
    + surrogateDiagTailX0RatChunk000Sub001Block107Part009
    + surrogateDiagTailX0RatChunk000Sub001Block107Part010
    + surrogateDiagTailX0RatChunk000Sub001Block107Part011
    + surrogateDiagTailX0RatChunk000Sub001Block107Part012
    + surrogateDiagTailX0RatChunk000Sub001Block107Part013
    + surrogateDiagTailX0RatChunk000Sub001Block107Part014
    + surrogateDiagTailX0RatChunk000Sub001Block107Part015
    + surrogateDiagTailX0RatChunk000Sub001Block107Part016
    + surrogateDiagTailX0RatChunk000Sub001Block107Part017
    + surrogateDiagTailX0RatChunk000Sub001Block107Part018
    + surrogateDiagTailX0RatChunk000Sub001Block107Part019
    + surrogateDiagTailX0RatChunk000Sub001Block107Part020
    + surrogateDiagTailX0RatChunk000Sub001Block107Part021
    + surrogateDiagTailX0RatChunk000Sub001Block107Part022
    + surrogateDiagTailX0RatChunk000Sub001Block107Part023
    + surrogateDiagTailX0RatChunk000Sub001Block107Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block107_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block107Head + surrogateDiagTailX0RatChunk000Sub001Block107Mid + surrogateDiagTailX0RatChunk000Sub001Block107Tail =
      surrogateDiagTailX0RatChunk000Sub001Block107 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block107Head surrogateDiagTailX0RatChunk000Sub001Block107Mid surrogateDiagTailX0RatChunk000Sub001Block107Tail surrogateDiagTailX0RatChunk000Sub001Block107
  ring

def SurrogateDiagonalTailChunk000Sub001Block107HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block107HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block107Head

def SurrogateDiagonalTailChunk000Sub001Block107MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block107MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block107Mid

def SurrogateDiagonalTailChunk000Sub001Block107TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block107TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block107Tail

theorem surrogateDiagonalTailChunk000Sub001Block107_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block107HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block107MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block107TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block107Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block107 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block107HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block107MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block107TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block107Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block107_eq_head_add_mid_add_tail

/-- Block 108 covers tail-support indices [7700,7725) and q from 12723 to 12763. -/

def TailChunk000Sub001Block108Part000SupportExplicit : Finset ℕ :=
  ([12723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part000 : ℚ :=
  (44947505219 : ℚ) / 258606992464281600

def SurrogateDiagonalTailChunk000Sub001Block108Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12723
    = surrogateDiagTailX0RatChunk000Sub001Block108Part000

theorem surrogateDiagonalTailChunk000Sub001Block108Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part000] using hcert

def TailChunk000Sub001Block108Part001SupportExplicit : Finset ℕ :=
  ([12727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part001 : ℚ :=
  (3875681401 : ℚ) / 207296167359283200

def SurrogateDiagonalTailChunk000Sub001Block108Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12727
    = surrogateDiagTailX0RatChunk000Sub001Block108Part001

theorem surrogateDiagonalTailChunk000Sub001Block108Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part001] using hcert

def TailChunk000Sub001Block108Part002SupportExplicit : Finset ℕ :=
  ([12729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part002 : ℚ :=
  (1124747668325 : ℚ) / 6477381888336120384

def SurrogateDiagonalTailChunk000Sub001Block108Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12729
    = surrogateDiagTailX0RatChunk000Sub001Block108Part002

theorem surrogateDiagonalTailChunk000Sub001Block108Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part002] using hcert

def TailChunk000Sub001Block108Part003SupportExplicit : Finset ℕ :=
  ([12730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part003 : ℚ :=
  (887355065525 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub001Block108Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12730
    = surrogateDiagTailX0RatChunk000Sub001Block108Part003

theorem surrogateDiagonalTailChunk000Sub001Block108Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part003] using hcert

def TailChunk000Sub001Block108Part004SupportExplicit : Finset ℕ :=
  ([12731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part004 : ℚ :=
  (38074349275 : ℚ) / 14141498602451415552

def SurrogateDiagonalTailChunk000Sub001Block108Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12731
    = surrogateDiagTailX0RatChunk000Sub001Block108Part004

theorem surrogateDiagonalTailChunk000Sub001Block108Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part004] using hcert

def TailChunk000Sub001Block108Part005SupportExplicit : Finset ℕ :=
  ([12733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part005 : ℚ :=
  (771952386625 : ℚ) / 26812372978696716288

def SurrogateDiagonalTailChunk000Sub001Block108Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12733
    = surrogateDiagTailX0RatChunk000Sub001Block108Part005

theorem surrogateDiagonalTailChunk000Sub001Block108Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part005] using hcert

def TailChunk000Sub001Block108Part006SupportExplicit : Finset ℕ :=
  ([12734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part006 : ℚ :=
  (633417015625 : ℚ) / 1026675987709924242

def SurrogateDiagonalTailChunk000Sub001Block108Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12734
    = surrogateDiagTailX0RatChunk000Sub001Block108Part006

theorem surrogateDiagonalTailChunk000Sub001Block108Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part006] using hcert

def TailChunk000Sub001Block108Part007SupportExplicit : Finset ℕ :=
  ([12737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part007 : ℚ :=
  (1921199123 : ℚ) / 1189989797417409600

def SurrogateDiagonalTailChunk000Sub001Block108Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12737
    = surrogateDiagTailX0RatChunk000Sub001Block108Part007

theorem surrogateDiagonalTailChunk000Sub001Block108Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part007] using hcert

def TailChunk000Sub001Block108Part008SupportExplicit : Finset ℕ :=
  ([12738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part008 : ℚ :=
  (50761096777 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub001Block108Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12738
    = surrogateDiagTailX0RatChunk000Sub001Block108Part008

theorem surrogateDiagonalTailChunk000Sub001Block108Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part008] using hcert

def TailChunk000Sub001Block108Part009SupportExplicit : Finset ℕ :=
  ([12739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block108Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12739
    = surrogateDiagTailX0RatChunk000Sub001Block108Part009

theorem surrogateDiagonalTailChunk000Sub001Block108Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part009] using hcert

def TailChunk000Sub001Block108Part010SupportExplicit : Finset ℕ :=
  ([12741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part010 : ℚ :=
  (45694362319 : ℚ) / 443452885578547200

def SurrogateDiagonalTailChunk000Sub001Block108Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12741
    = surrogateDiagTailX0RatChunk000Sub001Block108Part010

theorem surrogateDiagonalTailChunk000Sub001Block108Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part010] using hcert

def TailChunk000Sub001Block108Part011SupportExplicit : Finset ℕ :=
  ([12742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part011 : ℚ :=
  (24167141725 : ℚ) / 34333550408374272

def SurrogateDiagonalTailChunk000Sub001Block108Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12742
    = surrogateDiagTailX0RatChunk000Sub001Block108Part011

theorem surrogateDiagonalTailChunk000Sub001Block108Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part011] using hcert

def TailChunk000Sub001Block108Part012SupportExplicit : Finset ℕ :=
  ([12743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block108Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12743
    = surrogateDiagTailX0RatChunk000Sub001Block108Part012

theorem surrogateDiagonalTailChunk000Sub001Block108Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part012] using hcert

def TailChunk000Sub001Block108Part013SupportExplicit : Finset ℕ :=
  ([12745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part013 : ℚ :=
  (812626052725 : ℚ) / 26981402387623477248

def SurrogateDiagonalTailChunk000Sub001Block108Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12745
    = surrogateDiagTailX0RatChunk000Sub001Block108Part013

theorem surrogateDiagonalTailChunk000Sub001Block108Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part013] using hcert

def TailChunk000Sub001Block108Part014SupportExplicit : Finset ℕ :=
  ([12746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part014 : ℚ :=
  (634611390625 : ℚ) / 1030552060750470432

def SurrogateDiagonalTailChunk000Sub001Block108Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12746
    = surrogateDiagTailX0RatChunk000Sub001Block108Part014

theorem surrogateDiagonalTailChunk000Sub001Block108Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part014] using hcert

def TailChunk000Sub001Block108Part015SupportExplicit : Finset ℕ :=
  ([12747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part015 : ℚ :=
  (1197207318325 : ℚ) / 6992658831556528128

def SurrogateDiagonalTailChunk000Sub001Block108Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12747
    = surrogateDiagTailX0RatChunk000Sub001Block108Part015

theorem surrogateDiagonalTailChunk000Sub001Block108Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part015] using hcert

def TailChunk000Sub001Block108Part016SupportExplicit : Finset ℕ :=
  ([12749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part016 : ℚ :=
  (2084866693 : ℚ) / 136076105779200000

def SurrogateDiagonalTailChunk000Sub001Block108Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12749
    = surrogateDiagTailX0RatChunk000Sub001Block108Part016

theorem surrogateDiagonalTailChunk000Sub001Block108Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part016] using hcert

def TailChunk000Sub001Block108Part017SupportExplicit : Finset ℕ :=
  ([12751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part017 : ℚ :=
  (1444213689 : ℚ) / 788228867584000000

def SurrogateDiagonalTailChunk000Sub001Block108Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12751
    = surrogateDiagTailX0RatChunk000Sub001Block108Part017

theorem surrogateDiagonalTailChunk000Sub001Block108Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part017] using hcert

def TailChunk000Sub001Block108Part018SupportExplicit : Finset ℕ :=
  ([12754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part018 : ℚ :=
  (84971698327 : ℚ) / 88890924085891200

def SurrogateDiagonalTailChunk000Sub001Block108Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12754
    = surrogateDiagTailX0RatChunk000Sub001Block108Part018

theorem surrogateDiagonalTailChunk000Sub001Block108Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part018] using hcert

def TailChunk000Sub001Block108Part019SupportExplicit : Finset ℕ :=
  ([12755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part019 : ℚ :=
  (3261256949 : ℚ) / 216529729286400000

def SurrogateDiagonalTailChunk000Sub001Block108Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12755
    = surrogateDiagTailX0RatChunk000Sub001Block108Part019

theorem surrogateDiagonalTailChunk000Sub001Block108Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part019] using hcert

def TailChunk000Sub001Block108Part020SupportExplicit : Finset ℕ :=
  ([12757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block108Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12757
    = surrogateDiagTailX0RatChunk000Sub001Block108Part020

theorem surrogateDiagonalTailChunk000Sub001Block108Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part020] using hcert

def TailChunk000Sub001Block108Part021SupportExplicit : Finset ℕ :=
  ([12758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part021 : ℚ :=
  (635806890625 : ℚ) / 1034439098628845682

def SurrogateDiagonalTailChunk000Sub001Block108Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12758
    = surrogateDiagTailX0RatChunk000Sub001Block108Part021

theorem surrogateDiagonalTailChunk000Sub001Block108Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part021] using hcert

def TailChunk000Sub001Block108Part022SupportExplicit : Finset ℕ :=
  ([12759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part022 : ℚ :=
  (70662130075 : ℚ) / 817334596447483008

def SurrogateDiagonalTailChunk000Sub001Block108Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12759
    = surrogateDiagTailX0RatChunk000Sub001Block108Part022

theorem surrogateDiagonalTailChunk000Sub001Block108Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part022] using hcert

def TailChunk000Sub001Block108Part023SupportExplicit : Finset ℕ :=
  ([12761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part023 : ℚ :=
  (34670355475 : ℚ) / 1984051065641034816

def SurrogateDiagonalTailChunk000Sub001Block108Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12761
    = surrogateDiagTailX0RatChunk000Sub001Block108Part023

theorem surrogateDiagonalTailChunk000Sub001Block108Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part023] using hcert

def TailChunk000Sub001Block108Part024SupportExplicit : Finset ℕ :=
  ([12763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block108Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block108Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12763
    = surrogateDiagTailX0RatChunk000Sub001Block108Part024

theorem surrogateDiagonalTailChunk000Sub001Block108Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block108Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block108Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block108Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block108Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block108Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block108HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block108Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block108Part000
    + surrogateDiagTailX0RatChunk000Sub001Block108Part001
    + surrogateDiagTailX0RatChunk000Sub001Block108Part002
    + surrogateDiagTailX0RatChunk000Sub001Block108Part003
    + surrogateDiagTailX0RatChunk000Sub001Block108Part004
    + surrogateDiagTailX0RatChunk000Sub001Block108Part005
    + surrogateDiagTailX0RatChunk000Sub001Block108Part006
    + surrogateDiagTailX0RatChunk000Sub001Block108Part007
    + surrogateDiagTailX0RatChunk000Sub001Block108Part008
    + surrogateDiagTailX0RatChunk000Sub001Block108Part009

def surrogateDiagonalTailChunk000Sub001Block108MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block108Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block108Part010
    + surrogateDiagTailX0RatChunk000Sub001Block108Part011
    + surrogateDiagTailX0RatChunk000Sub001Block108Part012
    + surrogateDiagTailX0RatChunk000Sub001Block108Part013
    + surrogateDiagTailX0RatChunk000Sub001Block108Part014
    + surrogateDiagTailX0RatChunk000Sub001Block108Part015
    + surrogateDiagTailX0RatChunk000Sub001Block108Part016
    + surrogateDiagTailX0RatChunk000Sub001Block108Part017
    + surrogateDiagTailX0RatChunk000Sub001Block108Part018
    + surrogateDiagTailX0RatChunk000Sub001Block108Part019

def surrogateDiagonalTailChunk000Sub001Block108TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block108Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block108Part020
    + surrogateDiagTailX0RatChunk000Sub001Block108Part021
    + surrogateDiagTailX0RatChunk000Sub001Block108Part022
    + surrogateDiagTailX0RatChunk000Sub001Block108Part023
    + surrogateDiagTailX0RatChunk000Sub001Block108Part024

def surrogateDiagonalTailChunk000Sub001Block108Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block108HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block108MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block108TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block108 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block108Part000
    + surrogateDiagTailX0RatChunk000Sub001Block108Part001
    + surrogateDiagTailX0RatChunk000Sub001Block108Part002
    + surrogateDiagTailX0RatChunk000Sub001Block108Part003
    + surrogateDiagTailX0RatChunk000Sub001Block108Part004
    + surrogateDiagTailX0RatChunk000Sub001Block108Part005
    + surrogateDiagTailX0RatChunk000Sub001Block108Part006
    + surrogateDiagTailX0RatChunk000Sub001Block108Part007
    + surrogateDiagTailX0RatChunk000Sub001Block108Part008
    + surrogateDiagTailX0RatChunk000Sub001Block108Part009
    + surrogateDiagTailX0RatChunk000Sub001Block108Part010
    + surrogateDiagTailX0RatChunk000Sub001Block108Part011
    + surrogateDiagTailX0RatChunk000Sub001Block108Part012
    + surrogateDiagTailX0RatChunk000Sub001Block108Part013
    + surrogateDiagTailX0RatChunk000Sub001Block108Part014
    + surrogateDiagTailX0RatChunk000Sub001Block108Part015
    + surrogateDiagTailX0RatChunk000Sub001Block108Part016
    + surrogateDiagTailX0RatChunk000Sub001Block108Part017
    + surrogateDiagTailX0RatChunk000Sub001Block108Part018
    + surrogateDiagTailX0RatChunk000Sub001Block108Part019
    + surrogateDiagTailX0RatChunk000Sub001Block108Part020
    + surrogateDiagTailX0RatChunk000Sub001Block108Part021
    + surrogateDiagTailX0RatChunk000Sub001Block108Part022
    + surrogateDiagTailX0RatChunk000Sub001Block108Part023
    + surrogateDiagTailX0RatChunk000Sub001Block108Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block108_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block108Head + surrogateDiagTailX0RatChunk000Sub001Block108Mid + surrogateDiagTailX0RatChunk000Sub001Block108Tail =
      surrogateDiagTailX0RatChunk000Sub001Block108 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block108Head surrogateDiagTailX0RatChunk000Sub001Block108Mid surrogateDiagTailX0RatChunk000Sub001Block108Tail surrogateDiagTailX0RatChunk000Sub001Block108
  ring

def SurrogateDiagonalTailChunk000Sub001Block108HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block108HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block108Head

def SurrogateDiagonalTailChunk000Sub001Block108MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block108MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block108Mid

def SurrogateDiagonalTailChunk000Sub001Block108TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block108TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block108Tail

theorem surrogateDiagonalTailChunk000Sub001Block108_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block108HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block108MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block108TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block108Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block108 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block108HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block108MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block108TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block108Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block108_eq_head_add_mid_add_tail

/-- Block 109 covers tail-support indices [7725,7750) and q from 12765 to 12803. -/

def TailChunk000Sub001Block109Part000SupportExplicit : Finset ℕ :=
  ([12765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part000 : ℚ :=
  (108860479025 : ℚ) / 366348863042224128

def SurrogateDiagonalTailChunk000Sub001Block109Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12765
    = surrogateDiagTailX0RatChunk000Sub001Block109Part000

theorem surrogateDiagonalTailChunk000Sub001Block109Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part000] using hcert

def TailChunk000Sub001Block109Part001SupportExplicit : Finset ℕ :=
  ([12766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part001 : ℚ :=
  (92005326121 : ℚ) / 119562821318707200

def SurrogateDiagonalTailChunk000Sub001Block109Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12766
    = surrogateDiagTailX0RatChunk000Sub001Block109Part001

theorem surrogateDiagonalTailChunk000Sub001Block109Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part001] using hcert

def TailChunk000Sub001Block109Part002SupportExplicit : Finset ℕ :=
  ([12767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part002 : ℚ :=
  (5015933237 : ℚ) / 1037007360000000000

def SurrogateDiagonalTailChunk000Sub001Block109Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12767
    = surrogateDiagTailX0RatChunk000Sub001Block109Part002

theorem surrogateDiagonalTailChunk000Sub001Block109Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part002] using hcert

def TailChunk000Sub001Block109Part003SupportExplicit : Finset ℕ :=
  ([12770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part003 : ℚ :=
  (967537748825 : ℚ) / 848475929085886464

def SurrogateDiagonalTailChunk000Sub001Block109Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12770
    = surrogateDiagTailX0RatChunk000Sub001Block109Part003

theorem surrogateDiagonalTailChunk000Sub001Block109Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part003] using hcert

def TailChunk000Sub001Block109Part004SupportExplicit : Finset ℕ :=
  ([12773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part004 : ℚ :=
  (366616867 : ℚ) / 242630387375800320

def SurrogateDiagonalTailChunk000Sub001Block109Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12773
    = surrogateDiagTailX0RatChunk000Sub001Block109Part004

theorem surrogateDiagonalTailChunk000Sub001Block109Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part004] using hcert

def TailChunk000Sub001Block109Part005SupportExplicit : Finset ℕ :=
  ([12774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part005 : ℚ :=
  (3466875 : ℚ) / 1673980542976

def SurrogateDiagonalTailChunk000Sub001Block109Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12774
    = surrogateDiagTailX0RatChunk000Sub001Block109Part005

theorem surrogateDiagonalTailChunk000Sub001Block109Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part005] using hcert

def TailChunk000Sub001Block109Part006SupportExplicit : Finset ℕ :=
  ([12777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part006 : ℚ :=
  (566892665525 : ℚ) / 6575661888565752384

def SurrogateDiagonalTailChunk000Sub001Block109Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12777
    = surrogateDiagTailX0RatChunk000Sub001Block109Part006

theorem surrogateDiagonalTailChunk000Sub001Block109Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part006] using hcert

def TailChunk000Sub001Block109Part007SupportExplicit : Finset ℕ :=
  ([12778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part007 : ℚ :=
  (637801890625 : ℚ) / 1040941917519112992

def SurrogateDiagonalTailChunk000Sub001Block109Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12778
    = surrogateDiagTailX0RatChunk000Sub001Block109Part007

theorem surrogateDiagonalTailChunk000Sub001Block109Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part007] using hcert

def TailChunk000Sub001Block109Part008SupportExplicit : Finset ℕ :=
  ([12779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part008 : ℚ :=
  (304863001375 : ℚ) / 48216734497051527168

def SurrogateDiagonalTailChunk000Sub001Block109Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12779
    = surrogateDiagTailX0RatChunk000Sub001Block109Part008

theorem surrogateDiagonalTailChunk000Sub001Block109Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part008] using hcert

def TailChunk000Sub001Block109Part009SupportExplicit : Finset ℕ :=
  ([12781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block109Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12781
    = surrogateDiagTailX0RatChunk000Sub001Block109Part009

theorem surrogateDiagonalTailChunk000Sub001Block109Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part009] using hcert

def TailChunk000Sub001Block109Part010SupportExplicit : Finset ℕ :=
  ([12782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part010 : ℚ :=
  (75289944061 : ℚ) / 58606699092019200

def SurrogateDiagonalTailChunk000Sub001Block109Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12782
    = surrogateDiagTailX0RatChunk000Sub001Block109Part010

theorem surrogateDiagonalTailChunk000Sub001Block109Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part010] using hcert

def TailChunk000Sub001Block109Part011SupportExplicit : Finset ℕ :=
  ([12783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part011 : ℚ :=
  (1134850081 : ℚ) / 13176050113486080

def SurrogateDiagonalTailChunk000Sub001Block109Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12783
    = surrogateDiagTailX0RatChunk000Sub001Block109Part011

theorem surrogateDiagonalTailChunk000Sub001Block109Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part011] using hcert

def TailChunk000Sub001Block109Part012SupportExplicit : Finset ℕ :=
  ([12785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part012 : ℚ :=
  (3839103425 : ℚ) / 128271631527346176

def SurrogateDiagonalTailChunk000Sub001Block109Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12785
    = surrogateDiagTailX0RatChunk000Sub001Block109Part012

theorem surrogateDiagonalTailChunk000Sub001Block109Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part012] using hcert

def TailChunk000Sub001Block109Part013SupportExplicit : Finset ℕ :=
  ([12786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part013 : ℚ :=
  (11352479789 : ℚ) / 16470062641857600

def SurrogateDiagonalTailChunk000Sub001Block109Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12786
    = surrogateDiagTailX0RatChunk000Sub001Block109Part013

theorem surrogateDiagonalTailChunk000Sub001Block109Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part013] using hcert

def TailChunk000Sub001Block109Part014SupportExplicit : Finset ℕ :=
  ([12787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part014 : ℚ :=
  (231097852675 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk000Sub001Block109Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12787
    = surrogateDiagTailX0RatChunk000Sub001Block109Part014

theorem surrogateDiagonalTailChunk000Sub001Block109Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part014] using hcert

def TailChunk000Sub001Block109Part015SupportExplicit : Finset ℕ :=
  ([12790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part015 : ℚ :=
  (204662992175 : ℚ) / 853808047353897984

def SurrogateDiagonalTailChunk000Sub001Block109Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12790
    = surrogateDiagTailX0RatChunk000Sub001Block109Part015

theorem surrogateDiagonalTailChunk000Sub001Block109Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part015] using hcert

def TailChunk000Sub001Block109Part016SupportExplicit : Finset ℕ :=
  ([12791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block109Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12791
    = surrogateDiagTailX0RatChunk000Sub001Block109Part016

theorem surrogateDiagonalTailChunk000Sub001Block109Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part016] using hcert

def TailChunk000Sub001Block109Part017SupportExplicit : Finset ℕ :=
  ([12793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part017 : ℚ :=
  (4093885 : ℚ) / 439403250917568

def SurrogateDiagonalTailChunk000Sub001Block109Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12793
    = surrogateDiagTailX0RatChunk000Sub001Block109Part017

theorem surrogateDiagonalTailChunk000Sub001Block109Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part017] using hcert

def TailChunk000Sub001Block109Part018SupportExplicit : Finset ℕ :=
  ([12794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block109Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12794
    = surrogateDiagTailX0RatChunk000Sub001Block109Part018

theorem surrogateDiagonalTailChunk000Sub001Block109Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part018] using hcert

def TailChunk000Sub001Block109Part019SupportExplicit : Finset ℕ :=
  ([12795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part019 : ℚ :=
  (1227480616975 : ℚ) / 5396910126483898368

def SurrogateDiagonalTailChunk000Sub001Block109Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12795
    = surrogateDiagTailX0RatChunk000Sub001Block109Part019

theorem surrogateDiagonalTailChunk000Sub001Block109Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part019] using hcert

def TailChunk000Sub001Block109Part020SupportExplicit : Finset ℕ :=
  ([12797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part020 : ℚ :=
  (63273701 : ℚ) / 49466022631401024

def SurrogateDiagonalTailChunk000Sub001Block109Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12797
    = surrogateDiagTailX0RatChunk000Sub001Block109Part020

theorem surrogateDiagonalTailChunk000Sub001Block109Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part020] using hcert

def TailChunk000Sub001Block109Part021SupportExplicit : Finset ℕ :=
  ([12799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block109Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12799
    = surrogateDiagTailX0RatChunk000Sub001Block109Part021

theorem surrogateDiagonalTailChunk000Sub001Block109Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part021] using hcert

def TailChunk000Sub001Block109Part022SupportExplicit : Finset ℕ :=
  ([12801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part022 : ℚ :=
  (46025265697 : ℚ) / 409681920000000000

def SurrogateDiagonalTailChunk000Sub001Block109Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12801
    = surrogateDiagTailX0RatChunk000Sub001Block109Part022

theorem surrogateDiagonalTailChunk000Sub001Block109Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part022] using hcert

def TailChunk000Sub001Block109Part023SupportExplicit : Finset ℕ :=
  ([12802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part023 : ℚ :=
  (32278703825 : ℚ) / 1837894820796186624

def SurrogateDiagonalTailChunk000Sub001Block109Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12802
    = surrogateDiagTailX0RatChunk000Sub001Block109Part023

theorem surrogateDiagonalTailChunk000Sub001Block109Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part023] using hcert

def TailChunk000Sub001Block109Part024SupportExplicit : Finset ℕ :=
  ([12803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block109Part024 : ℚ :=
  (5831592599 : ℚ) / 237639615238563840

def SurrogateDiagonalTailChunk000Sub001Block109Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 12803
    = surrogateDiagTailX0RatChunk000Sub001Block109Part024

theorem surrogateDiagonalTailChunk000Sub001Block109Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block109Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block109Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block109Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block109Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block109Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block109HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block109Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block109Part000
    + surrogateDiagTailX0RatChunk000Sub001Block109Part001
    + surrogateDiagTailX0RatChunk000Sub001Block109Part002
    + surrogateDiagTailX0RatChunk000Sub001Block109Part003
    + surrogateDiagTailX0RatChunk000Sub001Block109Part004
    + surrogateDiagTailX0RatChunk000Sub001Block109Part005
    + surrogateDiagTailX0RatChunk000Sub001Block109Part006
    + surrogateDiagTailX0RatChunk000Sub001Block109Part007
    + surrogateDiagTailX0RatChunk000Sub001Block109Part008
    + surrogateDiagTailX0RatChunk000Sub001Block109Part009

def surrogateDiagonalTailChunk000Sub001Block109MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block109Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block109Part010
    + surrogateDiagTailX0RatChunk000Sub001Block109Part011
    + surrogateDiagTailX0RatChunk000Sub001Block109Part012
    + surrogateDiagTailX0RatChunk000Sub001Block109Part013
    + surrogateDiagTailX0RatChunk000Sub001Block109Part014
    + surrogateDiagTailX0RatChunk000Sub001Block109Part015
    + surrogateDiagTailX0RatChunk000Sub001Block109Part016
    + surrogateDiagTailX0RatChunk000Sub001Block109Part017
    + surrogateDiagTailX0RatChunk000Sub001Block109Part018
    + surrogateDiagTailX0RatChunk000Sub001Block109Part019

def surrogateDiagonalTailChunk000Sub001Block109TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block109Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block109Part020
    + surrogateDiagTailX0RatChunk000Sub001Block109Part021
    + surrogateDiagTailX0RatChunk000Sub001Block109Part022
    + surrogateDiagTailX0RatChunk000Sub001Block109Part023
    + surrogateDiagTailX0RatChunk000Sub001Block109Part024

def surrogateDiagonalTailChunk000Sub001Block109Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block109HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block109MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block109TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block109 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block109Part000
    + surrogateDiagTailX0RatChunk000Sub001Block109Part001
    + surrogateDiagTailX0RatChunk000Sub001Block109Part002
    + surrogateDiagTailX0RatChunk000Sub001Block109Part003
    + surrogateDiagTailX0RatChunk000Sub001Block109Part004
    + surrogateDiagTailX0RatChunk000Sub001Block109Part005
    + surrogateDiagTailX0RatChunk000Sub001Block109Part006
    + surrogateDiagTailX0RatChunk000Sub001Block109Part007
    + surrogateDiagTailX0RatChunk000Sub001Block109Part008
    + surrogateDiagTailX0RatChunk000Sub001Block109Part009
    + surrogateDiagTailX0RatChunk000Sub001Block109Part010
    + surrogateDiagTailX0RatChunk000Sub001Block109Part011
    + surrogateDiagTailX0RatChunk000Sub001Block109Part012
    + surrogateDiagTailX0RatChunk000Sub001Block109Part013
    + surrogateDiagTailX0RatChunk000Sub001Block109Part014
    + surrogateDiagTailX0RatChunk000Sub001Block109Part015
    + surrogateDiagTailX0RatChunk000Sub001Block109Part016
    + surrogateDiagTailX0RatChunk000Sub001Block109Part017
    + surrogateDiagTailX0RatChunk000Sub001Block109Part018
    + surrogateDiagTailX0RatChunk000Sub001Block109Part019
    + surrogateDiagTailX0RatChunk000Sub001Block109Part020
    + surrogateDiagTailX0RatChunk000Sub001Block109Part021
    + surrogateDiagTailX0RatChunk000Sub001Block109Part022
    + surrogateDiagTailX0RatChunk000Sub001Block109Part023
    + surrogateDiagTailX0RatChunk000Sub001Block109Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block109_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block109Head + surrogateDiagTailX0RatChunk000Sub001Block109Mid + surrogateDiagTailX0RatChunk000Sub001Block109Tail =
      surrogateDiagTailX0RatChunk000Sub001Block109 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block109Head surrogateDiagTailX0RatChunk000Sub001Block109Mid surrogateDiagTailX0RatChunk000Sub001Block109Tail surrogateDiagTailX0RatChunk000Sub001Block109
  ring

def SurrogateDiagonalTailChunk000Sub001Block109HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block109HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block109Head

def SurrogateDiagonalTailChunk000Sub001Block109MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block109MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block109Mid

def SurrogateDiagonalTailChunk000Sub001Block109TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block109TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block109Tail

theorem surrogateDiagonalTailChunk000Sub001Block109_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block109HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block109MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block109TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block109Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block109 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block109HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block109MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block109TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block109Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block109_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

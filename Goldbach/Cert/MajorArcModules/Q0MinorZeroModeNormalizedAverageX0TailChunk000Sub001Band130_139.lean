import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [130,140). -/

/-- Block 130 covers tail-support indices [8250,8275) and q from 13627 to 13665. -/

def TailChunk000Sub001Block130Part000SupportExplicit : Finset ℕ :=
  ([13627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part000 : ℚ :=
  (2901486390625 : ℚ) / 21549659181491903922

def SurrogateDiagonalTailChunk000Sub001Block130Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13627
    = surrogateDiagTailX0RatChunk000Sub001Block130Part000

theorem surrogateDiagonalTailChunk000Sub001Block130Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part000] using hcert

def TailChunk000Sub001Block130Part001SupportExplicit : Finset ℕ :=
  ([13629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part001 : ℚ :=
  (28137697043 : ℚ) / 46941158565642240

def SurrogateDiagonalTailChunk000Sub001Block130Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13629
    = surrogateDiagTailX0RatChunk000Sub001Block130Part001

theorem surrogateDiagonalTailChunk000Sub001Block130Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part001] using hcert

def TailChunk000Sub001Block130Part002SupportExplicit : Finset ℕ :=
  ([13630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part002 : ℚ :=
  (1028607515675 : ℚ) / 880846596536008704

def SurrogateDiagonalTailChunk000Sub001Block130Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13630
    = surrogateDiagTailX0RatChunk000Sub001Block130Part002

theorem surrogateDiagonalTailChunk000Sub001Block130Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part002] using hcert

def TailChunk000Sub001Block130Part003SupportExplicit : Finset ℕ :=
  ([13631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part003 : ℚ :=
  (205873077425 : ℚ) / 1436741350040005632

def SurrogateDiagonalTailChunk000Sub001Block130Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13631
    = surrogateDiagTailX0RatChunk000Sub001Block130Part003

theorem surrogateDiagonalTailChunk000Sub001Block130Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part003] using hcert

def TailChunk000Sub001Block130Part004SupportExplicit : Finset ℕ :=
  ([13633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part004 : ℚ :=
  (2904042015625 : ℚ) / 21587640505935593472

def SurrogateDiagonalTailChunk000Sub001Block130Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13633
    = surrogateDiagTailX0RatChunk000Sub001Block130Part004

theorem surrogateDiagonalTailChunk000Sub001Block130Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part004] using hcert

def TailChunk000Sub001Block130Part005SupportExplicit : Finset ℕ :=
  ([13634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part005 : ℚ :=
  (107419446127 : ℚ) / 167805714432000000

def SurrogateDiagonalTailChunk000Sub001Block130Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13634
    = surrogateDiagTailX0RatChunk000Sub001Block130Part005

theorem surrogateDiagonalTailChunk000Sub001Block130Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part005] using hcert

def TailChunk000Sub001Block130Part006SupportExplicit : Finset ℕ :=
  ([13637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part006 : ℚ :=
  (1694034896575 : ℚ) / 10424271721691086848

def SurrogateDiagonalTailChunk000Sub001Block130Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13637
    = surrogateDiagTailX0RatChunk000Sub001Block130Part006

theorem surrogateDiagonalTailChunk000Sub001Block130Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part006] using hcert

def TailChunk000Sub001Block130Part007SupportExplicit : Finset ℕ :=
  ([13638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part007 : ℚ :=
  (193636875 : ℚ) / 106584315265024

def SurrogateDiagonalTailChunk000Sub001Block130Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13638
    = surrogateDiagTailX0RatChunk000Sub001Block130Part007

theorem surrogateDiagonalTailChunk000Sub001Block130Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part007] using hcert

def TailChunk000Sub001Block130Part008SupportExplicit : Finset ℕ :=
  ([13639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part008 : ℚ :=
  (21021206375 : ℚ) / 140518805090509824

def SurrogateDiagonalTailChunk000Sub001Block130Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13639
    = surrogateDiagTailX0RatChunk000Sub001Block130Part008

theorem surrogateDiagonalTailChunk000Sub001Block130Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part008] using hcert

def TailChunk000Sub001Block130Part009SupportExplicit : Finset ℕ :=
  ([13641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part009 : ℚ :=
  (403738711225 : ℚ) / 1067934420488902728

def SurrogateDiagonalTailChunk000Sub001Block130Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13641
    = surrogateDiagTailX0RatChunk000Sub001Block130Part009

theorem surrogateDiagonalTailChunk000Sub001Block130Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part009] using hcert

def TailChunk000Sub001Block130Part010SupportExplicit : Finset ℕ :=
  ([13642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part010 : ℚ :=
  (676388904625 : ℚ) / 1077926117001537312

def SurrogateDiagonalTailChunk000Sub001Block130Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13642
    = surrogateDiagTailX0RatChunk000Sub001Block130Part010

theorem surrogateDiagonalTailChunk000Sub001Block130Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part010] using hcert

def TailChunk000Sub001Block130Part011SupportExplicit : Finset ℕ :=
  ([13643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part011 : ℚ :=
  (2253834154075 : ℚ) / 11666153306677473792

def SurrogateDiagonalTailChunk000Sub001Block130Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13643
    = surrogateDiagTailX0RatChunk000Sub001Block130Part011

theorem surrogateDiagonalTailChunk000Sub001Block130Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part011] using hcert

def TailChunk000Sub001Block130Part012SupportExplicit : Finset ℕ :=
  ([13645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part012 : ℚ :=
  (7909102590475 : ℚ) / 35452289588113440768

def SurrogateDiagonalTailChunk000Sub001Block130Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13645
    = surrogateDiagTailX0RatChunk000Sub001Block130Part012

theorem surrogateDiagonalTailChunk000Sub001Block130Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part012] using hcert

def TailChunk000Sub001Block130Part013SupportExplicit : Finset ℕ :=
  ([13646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part013 : ℚ :=
  (727395765625 : ℚ) / 1353984609535762482

def SurrogateDiagonalTailChunk000Sub001Block130Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13646
    = surrogateDiagTailX0RatChunk000Sub001Block130Part013

theorem surrogateDiagonalTailChunk000Sub001Block130Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part013] using hcert

def TailChunk000Sub001Block130Part014SupportExplicit : Finset ℕ :=
  ([13647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part014 : ℚ :=
  (3232752019475 : ℚ) / 8558520001016177664

def SurrogateDiagonalTailChunk000Sub001Block130Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13647
    = surrogateDiagTailX0RatChunk000Sub001Block130Part014

theorem surrogateDiagonalTailChunk000Sub001Block130Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part014] using hcert

def TailChunk000Sub001Block130Part015SupportExplicit : Finset ℕ :=
  ([13649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block130Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13649
    = surrogateDiagTailX0RatChunk000Sub001Block130Part015

theorem surrogateDiagonalTailChunk000Sub001Block130Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part015] using hcert

def TailChunk000Sub001Block130Part016SupportExplicit : Finset ℕ :=
  ([13651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part016 : ℚ :=
  (11902010303 : ℚ) / 880778633910681600

def SurrogateDiagonalTailChunk000Sub001Block130Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13651
    = surrogateDiagTailX0RatChunk000Sub001Block130Part016

theorem surrogateDiagonalTailChunk000Sub001Block130Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part016] using hcert

def TailChunk000Sub001Block130Part017SupportExplicit : Finset ℕ :=
  ([13654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block130Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13654
    = surrogateDiagTailX0RatChunk000Sub001Block130Part017

theorem surrogateDiagonalTailChunk000Sub001Block130Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part017] using hcert

def TailChunk000Sub001Block130Part018SupportExplicit : Finset ℕ :=
  ([13655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part018 : ℚ :=
  (3736456769 : ℚ) / 284450957074851840

def SurrogateDiagonalTailChunk000Sub001Block130Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13655
    = surrogateDiagTailX0RatChunk000Sub001Block130Part018

theorem surrogateDiagonalTailChunk000Sub001Block130Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part018] using hcert

def TailChunk000Sub001Block130Part019SupportExplicit : Finset ℕ :=
  ([13657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part019 : ℚ :=
  (9541844447 : ℚ) / 937130993721000000

def SurrogateDiagonalTailChunk000Sub001Block130Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13657
    = surrogateDiagTailX0RatChunk000Sub001Block130Part019

theorem surrogateDiagonalTailChunk000Sub001Block130Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part019] using hcert

def TailChunk000Sub001Block130Part020SupportExplicit : Finset ℕ :=
  ([13658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block130Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13658
    = surrogateDiagTailX0RatChunk000Sub001Block130Part020

theorem surrogateDiagonalTailChunk000Sub001Block130Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part020] using hcert

def TailChunk000Sub001Block130Part021SupportExplicit : Finset ℕ :=
  ([13659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part021 : ℚ :=
  (1307153223625 : ℚ) / 14563889002232414208

def SurrogateDiagonalTailChunk000Sub001Block130Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13659
    = surrogateDiagTailX0RatChunk000Sub001Block130Part021

theorem surrogateDiagonalTailChunk000Sub001Block130Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part021] using hcert

def TailChunk000Sub001Block130Part022SupportExplicit : Finset ℕ :=
  ([13661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part022 : ℚ :=
  (230893284625 : ℚ) / 69761314649560745088

def SurrogateDiagonalTailChunk000Sub001Block130Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13661
    = surrogateDiagTailX0RatChunk000Sub001Block130Part022

theorem surrogateDiagonalTailChunk000Sub001Block130Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part022] using hcert

def TailChunk000Sub001Block130Part023SupportExplicit : Finset ℕ :=
  ([13663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part023 : ℚ :=
  (309340783 : ℚ) / 56021730105600000

def SurrogateDiagonalTailChunk000Sub001Block130Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13663
    = surrogateDiagTailX0RatChunk000Sub001Block130Part023

theorem surrogateDiagonalTailChunk000Sub001Block130Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part023] using hcert

def TailChunk000Sub001Block130Part024SupportExplicit : Finset ℕ :=
  ([13665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block130Part024 : ℚ :=
  (746634111 : ℚ) / 3745856224854016

def SurrogateDiagonalTailChunk000Sub001Block130Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13665
    = surrogateDiagTailX0RatChunk000Sub001Block130Part024

theorem surrogateDiagonalTailChunk000Sub001Block130Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block130Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block130Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block130Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block130Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block130Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block130Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block130HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block130Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block130Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block130Part000
    + surrogateDiagTailX0RatChunk000Sub001Block130Part001
    + surrogateDiagTailX0RatChunk000Sub001Block130Part002
    + surrogateDiagTailX0RatChunk000Sub001Block130Part003
    + surrogateDiagTailX0RatChunk000Sub001Block130Part004
    + surrogateDiagTailX0RatChunk000Sub001Block130Part005
    + surrogateDiagTailX0RatChunk000Sub001Block130Part006
    + surrogateDiagTailX0RatChunk000Sub001Block130Part007
    + surrogateDiagTailX0RatChunk000Sub001Block130Part008
    + surrogateDiagTailX0RatChunk000Sub001Block130Part009

def surrogateDiagonalTailChunk000Sub001Block130MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block130Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block130Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block130Part010
    + surrogateDiagTailX0RatChunk000Sub001Block130Part011
    + surrogateDiagTailX0RatChunk000Sub001Block130Part012
    + surrogateDiagTailX0RatChunk000Sub001Block130Part013
    + surrogateDiagTailX0RatChunk000Sub001Block130Part014
    + surrogateDiagTailX0RatChunk000Sub001Block130Part015
    + surrogateDiagTailX0RatChunk000Sub001Block130Part016
    + surrogateDiagTailX0RatChunk000Sub001Block130Part017
    + surrogateDiagTailX0RatChunk000Sub001Block130Part018
    + surrogateDiagTailX0RatChunk000Sub001Block130Part019

def surrogateDiagonalTailChunk000Sub001Block130TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block130Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block130Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block130Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block130Part020
    + surrogateDiagTailX0RatChunk000Sub001Block130Part021
    + surrogateDiagTailX0RatChunk000Sub001Block130Part022
    + surrogateDiagTailX0RatChunk000Sub001Block130Part023
    + surrogateDiagTailX0RatChunk000Sub001Block130Part024

def surrogateDiagonalTailChunk000Sub001Block130Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block130HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block130MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block130TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block130 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block130Part000
    + surrogateDiagTailX0RatChunk000Sub001Block130Part001
    + surrogateDiagTailX0RatChunk000Sub001Block130Part002
    + surrogateDiagTailX0RatChunk000Sub001Block130Part003
    + surrogateDiagTailX0RatChunk000Sub001Block130Part004
    + surrogateDiagTailX0RatChunk000Sub001Block130Part005
    + surrogateDiagTailX0RatChunk000Sub001Block130Part006
    + surrogateDiagTailX0RatChunk000Sub001Block130Part007
    + surrogateDiagTailX0RatChunk000Sub001Block130Part008
    + surrogateDiagTailX0RatChunk000Sub001Block130Part009
    + surrogateDiagTailX0RatChunk000Sub001Block130Part010
    + surrogateDiagTailX0RatChunk000Sub001Block130Part011
    + surrogateDiagTailX0RatChunk000Sub001Block130Part012
    + surrogateDiagTailX0RatChunk000Sub001Block130Part013
    + surrogateDiagTailX0RatChunk000Sub001Block130Part014
    + surrogateDiagTailX0RatChunk000Sub001Block130Part015
    + surrogateDiagTailX0RatChunk000Sub001Block130Part016
    + surrogateDiagTailX0RatChunk000Sub001Block130Part017
    + surrogateDiagTailX0RatChunk000Sub001Block130Part018
    + surrogateDiagTailX0RatChunk000Sub001Block130Part019
    + surrogateDiagTailX0RatChunk000Sub001Block130Part020
    + surrogateDiagTailX0RatChunk000Sub001Block130Part021
    + surrogateDiagTailX0RatChunk000Sub001Block130Part022
    + surrogateDiagTailX0RatChunk000Sub001Block130Part023
    + surrogateDiagTailX0RatChunk000Sub001Block130Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block130_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block130Head + surrogateDiagTailX0RatChunk000Sub001Block130Mid + surrogateDiagTailX0RatChunk000Sub001Block130Tail =
      surrogateDiagTailX0RatChunk000Sub001Block130 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block130Head surrogateDiagTailX0RatChunk000Sub001Block130Mid surrogateDiagTailX0RatChunk000Sub001Block130Tail surrogateDiagTailX0RatChunk000Sub001Block130
  ring

def SurrogateDiagonalTailChunk000Sub001Block130HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block130HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block130Head

def SurrogateDiagonalTailChunk000Sub001Block130MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block130MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block130Mid

def SurrogateDiagonalTailChunk000Sub001Block130TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block130TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block130Tail

theorem surrogateDiagonalTailChunk000Sub001Block130_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block130HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block130MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block130TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block130Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block130 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block130HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block130MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block130TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block130Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block130_eq_head_add_mid_add_tail

/-- Block 131 covers tail-support indices [8275,8300) and q from 13666 to 13706. -/

def TailChunk000Sub001Block131Part000SupportExplicit : Finset ℕ :=
  ([13666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13666
    = surrogateDiagTailX0RatChunk000Sub001Block131Part000

theorem surrogateDiagonalTailChunk000Sub001Block131Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part000] using hcert

def TailChunk000Sub001Block131Part001SupportExplicit : Finset ℕ :=
  ([13667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part001 : ℚ :=
  (303076225 : ℚ) / 316431049724873928

def SurrogateDiagonalTailChunk000Sub001Block131Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13667
    = surrogateDiagTailX0RatChunk000Sub001Block131Part001

theorem surrogateDiagonalTailChunk000Sub001Block131Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part001] using hcert

def TailChunk000Sub001Block131Part002SupportExplicit : Finset ℕ :=
  ([13669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13669
    = surrogateDiagTailX0RatChunk000Sub001Block131Part002

theorem surrogateDiagonalTailChunk000Sub001Block131Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part002] using hcert

def TailChunk000Sub001Block131Part003SupportExplicit : Finset ℕ :=
  ([13670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part003 : ℚ :=
  (77909835525 : ℚ) / 371465402911443968

def SurrogateDiagonalTailChunk000Sub001Block131Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13670
    = surrogateDiagTailX0RatChunk000Sub001Block131Part003

theorem surrogateDiagonalTailChunk000Sub001Block131Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part003] using hcert

def TailChunk000Sub001Block131Part004SupportExplicit : Finset ℕ :=
  ([13674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part004 : ℚ :=
  (72690532325 : ℚ) / 101138118071058432

def SurrogateDiagonalTailChunk000Sub001Block131Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13674
    = surrogateDiagTailX0RatChunk000Sub001Block131Part004

theorem surrogateDiagonalTailChunk000Sub001Block131Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part004] using hcert

def TailChunk000Sub001Block131Part005SupportExplicit : Finset ℕ :=
  ([13677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part005 : ℚ :=
  (326490899725 : ℚ) / 3803672433521590272

def SurrogateDiagonalTailChunk000Sub001Block131Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13677
    = surrogateDiagTailX0RatChunk000Sub001Block131Part005

theorem surrogateDiagonalTailChunk000Sub001Block131Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part005] using hcert

def TailChunk000Sub001Block131Part006SupportExplicit : Finset ℕ :=
  ([13678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part006 : ℚ :=
  (299316111775 : ℚ) / 2940567351785422848

def SurrogateDiagonalTailChunk000Sub001Block131Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13678
    = surrogateDiagTailX0RatChunk000Sub001Block131Part006

theorem surrogateDiagonalTailChunk000Sub001Block131Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part006] using hcert

def TailChunk000Sub001Block131Part007SupportExplicit : Finset ℕ :=
  ([13679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13679
    = surrogateDiagTailX0RatChunk000Sub001Block131Part007

theorem surrogateDiagonalTailChunk000Sub001Block131Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part007] using hcert

def TailChunk000Sub001Block131Part008SupportExplicit : Finset ℕ :=
  ([13681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13681
    = surrogateDiagTailX0RatChunk000Sub001Block131Part008

theorem surrogateDiagonalTailChunk000Sub001Block131Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part008] using hcert

def TailChunk000Sub001Block131Part009SupportExplicit : Finset ℕ :=
  ([13682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13682
    = surrogateDiagTailX0RatChunk000Sub001Block131Part009

theorem surrogateDiagonalTailChunk000Sub001Block131Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part009] using hcert

def TailChunk000Sub001Block131Part010SupportExplicit : Finset ℕ :=
  ([13683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part010 : ℚ :=
  (2600450147 : ℚ) / 34596822057615360

def SurrogateDiagonalTailChunk000Sub001Block131Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13683
    = surrogateDiagTailX0RatChunk000Sub001Block131Part010

theorem surrogateDiagonalTailChunk000Sub001Block131Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part010] using hcert

def TailChunk000Sub001Block131Part011SupportExplicit : Finset ℕ :=
  ([13685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part011 : ℚ :=
  (314033721775 : ℚ) / 3184069130638589952

def SurrogateDiagonalTailChunk000Sub001Block131Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13685
    = surrogateDiagTailX0RatChunk000Sub001Block131Part011

theorem surrogateDiagonalTailChunk000Sub001Block131Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part011] using hcert

def TailChunk000Sub001Block131Part012SupportExplicit : Finset ℕ :=
  ([13686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part012 : ℚ :=
  (13005898739 : ℚ) / 21623013786009600

def SurrogateDiagonalTailChunk000Sub001Block131Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13686
    = surrogateDiagTailX0RatChunk000Sub001Block131Part012

theorem surrogateDiagonalTailChunk000Sub001Block131Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part012] using hcert

def TailChunk000Sub001Block131Part013SupportExplicit : Finset ℕ :=
  ([13687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13687
    = surrogateDiagTailX0RatChunk000Sub001Block131Part013

theorem surrogateDiagonalTailChunk000Sub001Block131Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part013] using hcert

def TailChunk000Sub001Block131Part014SupportExplicit : Finset ℕ :=
  ([13691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13691
    = surrogateDiagTailX0RatChunk000Sub001Block131Part014

theorem surrogateDiagonalTailChunk000Sub001Block131Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part014] using hcert

def TailChunk000Sub001Block131Part015SupportExplicit : Finset ℕ :=
  ([13693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13693
    = surrogateDiagTailX0RatChunk000Sub001Block131Part015

theorem surrogateDiagonalTailChunk000Sub001Block131Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part015] using hcert

def TailChunk000Sub001Block131Part016SupportExplicit : Finset ℕ :=
  ([13694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part016 : ℚ :=
  (2486702419 : ℚ) / 194428160672563200

def SurrogateDiagonalTailChunk000Sub001Block131Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13694
    = surrogateDiagTailX0RatChunk000Sub001Block131Part016

theorem surrogateDiagonalTailChunk000Sub001Block131Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part016] using hcert

def TailChunk000Sub001Block131Part017SupportExplicit : Finset ℕ :=
  ([13695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part017 : ℚ :=
  (17997373419 : ℚ) / 61742036903526400

def SurrogateDiagonalTailChunk000Sub001Block131Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13695
    = surrogateDiagTailX0RatChunk000Sub001Block131Part017

theorem surrogateDiagonalTailChunk000Sub001Block131Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part017] using hcert

def TailChunk000Sub001Block131Part018SupportExplicit : Finset ℕ :=
  ([13697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block131Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13697
    = surrogateDiagTailX0RatChunk000Sub001Block131Part018

theorem surrogateDiagonalTailChunk000Sub001Block131Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part018] using hcert

def TailChunk000Sub001Block131Part019SupportExplicit : Finset ℕ :=
  ([13699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part019 : ℚ :=
  (94844298625 : ℚ) / 4091476475082442752

def SurrogateDiagonalTailChunk000Sub001Block131Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13699
    = surrogateDiagTailX0RatChunk000Sub001Block131Part019

theorem surrogateDiagonalTailChunk000Sub001Block131Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part019] using hcert

def TailChunk000Sub001Block131Part020SupportExplicit : Finset ℕ :=
  ([13701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part020 : ℚ :=
  (651823661675 : ℚ) / 8694817573846330944

def SurrogateDiagonalTailChunk000Sub001Block131Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13701
    = surrogateDiagTailX0RatChunk000Sub001Block131Part020

theorem surrogateDiagonalTailChunk000Sub001Block131Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part020] using hcert

def TailChunk000Sub001Block131Part021SupportExplicit : Finset ℕ :=
  ([13702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part021 : ℚ :=
  (94678613341 : ℚ) / 110097329238835200

def SurrogateDiagonalTailChunk000Sub001Block131Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13702
    = surrogateDiagTailX0RatChunk000Sub001Block131Part021

theorem surrogateDiagonalTailChunk000Sub001Block131Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part021] using hcert

def TailChunk000Sub001Block131Part022SupportExplicit : Finset ℕ :=
  ([13703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part022 : ℚ :=
  (16270703 : ℚ) / 16317511574224896

def SurrogateDiagonalTailChunk000Sub001Block131Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13703
    = surrogateDiagTailX0RatChunk000Sub001Block131Part022

theorem surrogateDiagonalTailChunk000Sub001Block131Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part022] using hcert

def TailChunk000Sub001Block131Part023SupportExplicit : Finset ℕ :=
  ([13705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part023 : ℚ :=
  (37580504509 : ℚ) / 1443208462631731200

def SurrogateDiagonalTailChunk000Sub001Block131Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13705
    = surrogateDiagTailX0RatChunk000Sub001Block131Part023

theorem surrogateDiagonalTailChunk000Sub001Block131Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part023] using hcert

def TailChunk000Sub001Block131Part024SupportExplicit : Finset ℕ :=
  ([13706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block131Part024 : ℚ :=
  (41972263499 : ℚ) / 38868031379865600

def SurrogateDiagonalTailChunk000Sub001Block131Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13706
    = surrogateDiagTailX0RatChunk000Sub001Block131Part024

theorem surrogateDiagonalTailChunk000Sub001Block131Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block131Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block131Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block131Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block131Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block131Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block131Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block131HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block131Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block131Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block131Part000
    + surrogateDiagTailX0RatChunk000Sub001Block131Part001
    + surrogateDiagTailX0RatChunk000Sub001Block131Part002
    + surrogateDiagTailX0RatChunk000Sub001Block131Part003
    + surrogateDiagTailX0RatChunk000Sub001Block131Part004
    + surrogateDiagTailX0RatChunk000Sub001Block131Part005
    + surrogateDiagTailX0RatChunk000Sub001Block131Part006
    + surrogateDiagTailX0RatChunk000Sub001Block131Part007
    + surrogateDiagTailX0RatChunk000Sub001Block131Part008
    + surrogateDiagTailX0RatChunk000Sub001Block131Part009

def surrogateDiagonalTailChunk000Sub001Block131MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block131Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block131Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block131Part010
    + surrogateDiagTailX0RatChunk000Sub001Block131Part011
    + surrogateDiagTailX0RatChunk000Sub001Block131Part012
    + surrogateDiagTailX0RatChunk000Sub001Block131Part013
    + surrogateDiagTailX0RatChunk000Sub001Block131Part014
    + surrogateDiagTailX0RatChunk000Sub001Block131Part015
    + surrogateDiagTailX0RatChunk000Sub001Block131Part016
    + surrogateDiagTailX0RatChunk000Sub001Block131Part017
    + surrogateDiagTailX0RatChunk000Sub001Block131Part018
    + surrogateDiagTailX0RatChunk000Sub001Block131Part019

def surrogateDiagonalTailChunk000Sub001Block131TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block131Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block131Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block131Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block131Part020
    + surrogateDiagTailX0RatChunk000Sub001Block131Part021
    + surrogateDiagTailX0RatChunk000Sub001Block131Part022
    + surrogateDiagTailX0RatChunk000Sub001Block131Part023
    + surrogateDiagTailX0RatChunk000Sub001Block131Part024

def surrogateDiagonalTailChunk000Sub001Block131Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block131HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block131MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block131TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block131 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block131Part000
    + surrogateDiagTailX0RatChunk000Sub001Block131Part001
    + surrogateDiagTailX0RatChunk000Sub001Block131Part002
    + surrogateDiagTailX0RatChunk000Sub001Block131Part003
    + surrogateDiagTailX0RatChunk000Sub001Block131Part004
    + surrogateDiagTailX0RatChunk000Sub001Block131Part005
    + surrogateDiagTailX0RatChunk000Sub001Block131Part006
    + surrogateDiagTailX0RatChunk000Sub001Block131Part007
    + surrogateDiagTailX0RatChunk000Sub001Block131Part008
    + surrogateDiagTailX0RatChunk000Sub001Block131Part009
    + surrogateDiagTailX0RatChunk000Sub001Block131Part010
    + surrogateDiagTailX0RatChunk000Sub001Block131Part011
    + surrogateDiagTailX0RatChunk000Sub001Block131Part012
    + surrogateDiagTailX0RatChunk000Sub001Block131Part013
    + surrogateDiagTailX0RatChunk000Sub001Block131Part014
    + surrogateDiagTailX0RatChunk000Sub001Block131Part015
    + surrogateDiagTailX0RatChunk000Sub001Block131Part016
    + surrogateDiagTailX0RatChunk000Sub001Block131Part017
    + surrogateDiagTailX0RatChunk000Sub001Block131Part018
    + surrogateDiagTailX0RatChunk000Sub001Block131Part019
    + surrogateDiagTailX0RatChunk000Sub001Block131Part020
    + surrogateDiagTailX0RatChunk000Sub001Block131Part021
    + surrogateDiagTailX0RatChunk000Sub001Block131Part022
    + surrogateDiagTailX0RatChunk000Sub001Block131Part023
    + surrogateDiagTailX0RatChunk000Sub001Block131Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block131_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block131Head + surrogateDiagTailX0RatChunk000Sub001Block131Mid + surrogateDiagTailX0RatChunk000Sub001Block131Tail =
      surrogateDiagTailX0RatChunk000Sub001Block131 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block131Head surrogateDiagTailX0RatChunk000Sub001Block131Mid surrogateDiagTailX0RatChunk000Sub001Block131Tail surrogateDiagTailX0RatChunk000Sub001Block131
  ring

def SurrogateDiagonalTailChunk000Sub001Block131HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block131HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block131Head

def SurrogateDiagonalTailChunk000Sub001Block131MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block131MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block131Mid

def SurrogateDiagonalTailChunk000Sub001Block131TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block131TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block131Tail

theorem surrogateDiagonalTailChunk000Sub001Block131_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block131HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block131MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block131TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block131Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block131 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block131HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block131MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block131TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block131Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block131_eq_head_add_mid_add_tail

/-- Block 132 covers tail-support indices [8300,8325) and q from 13709 to 13746. -/

def TailChunk000Sub001Block132Part000SupportExplicit : Finset ℕ :=
  ([13709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block132Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13709
    = surrogateDiagTailX0RatChunk000Sub001Block132Part000

theorem surrogateDiagonalTailChunk000Sub001Block132Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part000] using hcert

def TailChunk000Sub001Block132Part001SupportExplicit : Finset ℕ :=
  ([13710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part001 : ℚ :=
  (122611064425 : ℚ) / 36903276861456384

def SurrogateDiagonalTailChunk000Sub001Block132Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13710
    = surrogateDiagTailX0RatChunk000Sub001Block132Part001

theorem surrogateDiagonalTailChunk000Sub001Block132Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part001] using hcert

def TailChunk000Sub001Block132Part002SupportExplicit : Finset ℕ :=
  ([13711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block132Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13711
    = surrogateDiagTailX0RatChunk000Sub001Block132Part002

theorem surrogateDiagonalTailChunk000Sub001Block132Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part002] using hcert

def TailChunk000Sub001Block132Part003SupportExplicit : Finset ℕ :=
  ([13713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part003 : ℚ :=
  (652877342525 : ℚ) / 4685028426672390144

def SurrogateDiagonalTailChunk000Sub001Block132Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13713
    = surrogateDiagTailX0RatChunk000Sub001Block132Part003

theorem surrogateDiagonalTailChunk000Sub001Block132Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part003] using hcert

def TailChunk000Sub001Block132Part004SupportExplicit : Finset ℕ :=
  ([13714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part004 : ℚ :=
  (734663265625 : ℚ) / 1381179434669363712

def SurrogateDiagonalTailChunk000Sub001Block132Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13714
    = surrogateDiagTailX0RatChunk000Sub001Block132Part004

theorem surrogateDiagonalTailChunk000Sub001Block132Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part004] using hcert

def TailChunk000Sub001Block132Part005SupportExplicit : Finset ℕ :=
  ([13715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part005 : ℚ :=
  (43038281551 : ℚ) / 1032592529306419200

def SurrogateDiagonalTailChunk000Sub001Block132Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13715
    = surrogateDiagTailX0RatChunk000Sub001Block132Part005

theorem surrogateDiagonalTailChunk000Sub001Block132Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part005] using hcert

def TailChunk000Sub001Block132Part006SupportExplicit : Finset ℕ :=
  ([13717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part006 : ℚ :=
  (889552459 : ℚ) / 76520205643972608

def SurrogateDiagonalTailChunk000Sub001Block132Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13717
    = surrogateDiagTailX0RatChunk000Sub001Block132Part006

theorem surrogateDiagonalTailChunk000Sub001Block132Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part006] using hcert

def TailChunk000Sub001Block132Part007SupportExplicit : Finset ℕ :=
  ([13719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part007 : ℚ :=
  (1320798723025 : ℚ) / 13525893024042713088

def SurrogateDiagonalTailChunk000Sub001Block132Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13719
    = surrogateDiagTailX0RatChunk000Sub001Block132Part007

theorem surrogateDiagonalTailChunk000Sub001Block132Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part007] using hcert

def TailChunk000Sub001Block132Part008SupportExplicit : Finset ℕ :=
  ([13721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block132Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13721
    = surrogateDiagTailX0RatChunk000Sub001Block132Part008

theorem surrogateDiagonalTailChunk000Sub001Block132Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part008] using hcert

def TailChunk000Sub001Block132Part009SupportExplicit : Finset ℕ :=
  ([13722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part009 : ℚ :=
  (408486855025 : ℚ) / 273144056223827232

def SurrogateDiagonalTailChunk000Sub001Block132Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13722
    = surrogateDiagTailX0RatChunk000Sub001Block132Part009

theorem surrogateDiagonalTailChunk000Sub001Block132Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part009] using hcert

def TailChunk000Sub001Block132Part010SupportExplicit : Finset ℕ :=
  ([13723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block132Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13723
    = surrogateDiagTailX0RatChunk000Sub001Block132Part010

theorem surrogateDiagonalTailChunk000Sub001Block132Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part010] using hcert

def TailChunk000Sub001Block132Part011SupportExplicit : Finset ℕ :=
  ([13726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part011 : ℚ :=
  (735949515625 : ℚ) / 1386020719125292242

def SurrogateDiagonalTailChunk000Sub001Block132Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13726
    = surrogateDiagTailX0RatChunk000Sub001Block132Part011

theorem surrogateDiagonalTailChunk000Sub001Block132Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part011] using hcert

def TailChunk000Sub001Block132Part012SupportExplicit : Finset ℕ :=
  ([13727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part012 : ℚ :=
  (102686719625 : ℚ) / 4974681161164455936

def SurrogateDiagonalTailChunk000Sub001Block132Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13727
    = surrogateDiagTailX0RatChunk000Sub001Block132Part012

theorem surrogateDiagonalTailChunk000Sub001Block132Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part012] using hcert

def TailChunk000Sub001Block132Part013SupportExplicit : Finset ℕ :=
  ([13729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block132Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13729
    = surrogateDiagTailX0RatChunk000Sub001Block132Part013

theorem surrogateDiagonalTailChunk000Sub001Block132Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part013] using hcert

def TailChunk000Sub001Block132Part014SupportExplicit : Finset ℕ :=
  ([13730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part014 : ℚ :=
  (100917222825 : ℚ) / 108010002205278208

def SurrogateDiagonalTailChunk000Sub001Block132Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13730
    = surrogateDiagTailX0RatChunk000Sub001Block132Part014

theorem surrogateDiagonalTailChunk000Sub001Block132Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part014] using hcert

def TailChunk000Sub001Block132Part015SupportExplicit : Finset ℕ :=
  ([13731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part015 : ℚ :=
  (41163200825 : ℚ) / 450140767988687424

def SurrogateDiagonalTailChunk000Sub001Block132Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13731
    = surrogateDiagTailX0RatChunk000Sub001Block132Part015

theorem surrogateDiagonalTailChunk000Sub001Block132Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part015] using hcert

def TailChunk000Sub001Block132Part016SupportExplicit : Finset ℕ :=
  ([13733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part016 : ℚ :=
  (956026247 : ℚ) / 515358799845739200

def SurrogateDiagonalTailChunk000Sub001Block132Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13733
    = surrogateDiagTailX0RatChunk000Sub001Block132Part016

theorem surrogateDiagonalTailChunk000Sub001Block132Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part016] using hcert

def TailChunk000Sub001Block132Part017SupportExplicit : Finset ℕ :=
  ([13735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part017 : ℚ :=
  (2517020831 : ℚ) / 138197444906188800

def SurrogateDiagonalTailChunk000Sub001Block132Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13735
    = surrogateDiagTailX0RatChunk000Sub001Block132Part017

theorem surrogateDiagonalTailChunk000Sub001Block132Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part017] using hcert

def TailChunk000Sub001Block132Part018SupportExplicit : Finset ℕ :=
  ([13737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part018 : ℚ :=
  (53009676127 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk000Sub001Block132Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13737
    = surrogateDiagTailX0RatChunk000Sub001Block132Part018

theorem surrogateDiagonalTailChunk000Sub001Block132Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part018] using hcert

def TailChunk000Sub001Block132Part019SupportExplicit : Finset ℕ :=
  ([13738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part019 : ℚ :=
  (737236890625 : ℚ) / 1390874719627421472

def SurrogateDiagonalTailChunk000Sub001Block132Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13738
    = surrogateDiagTailX0RatChunk000Sub001Block132Part019

theorem surrogateDiagonalTailChunk000Sub001Block132Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part019] using hcert

def TailChunk000Sub001Block132Part020SupportExplicit : Finset ℕ :=
  ([13739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part020 : ℚ :=
  (15690785029 : ℚ) / 2426303873758003200

def SurrogateDiagonalTailChunk000Sub001Block132Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13739
    = surrogateDiagTailX0RatChunk000Sub001Block132Part020

theorem surrogateDiagonalTailChunk000Sub001Block132Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part020] using hcert

def TailChunk000Sub001Block132Part021SupportExplicit : Finset ℕ :=
  ([13741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part021 : ℚ :=
  (1390222219 : ℚ) / 54430442311680000

def SurrogateDiagonalTailChunk000Sub001Block132Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13741
    = surrogateDiagTailX0RatChunk000Sub001Block132Part021

theorem surrogateDiagonalTailChunk000Sub001Block132Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part021] using hcert

def TailChunk000Sub001Block132Part022SupportExplicit : Finset ℕ :=
  ([13742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part022 : ℚ :=
  (1180266025 : ℚ) / 2227992879083922

def SurrogateDiagonalTailChunk000Sub001Block132Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13742
    = surrogateDiagTailX0RatChunk000Sub001Block132Part022

theorem surrogateDiagonalTailChunk000Sub001Block132Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part022] using hcert

def TailChunk000Sub001Block132Part023SupportExplicit : Finset ℕ :=
  ([13745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part023 : ℚ :=
  (314999837575 : ℚ) / 12167811776970326016

def SurrogateDiagonalTailChunk000Sub001Block132Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13745
    = surrogateDiagTailX0RatChunk000Sub001Block132Part023

theorem surrogateDiagonalTailChunk000Sub001Block132Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part023] using hcert

def TailChunk000Sub001Block132Part024SupportExplicit : Finset ℕ :=
  ([13746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block132Part024 : ℚ :=
  (1553991844675 : ℚ) / 910243062639525888

def SurrogateDiagonalTailChunk000Sub001Block132Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13746
    = surrogateDiagTailX0RatChunk000Sub001Block132Part024

theorem surrogateDiagonalTailChunk000Sub001Block132Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block132Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block132Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block132Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block132Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block132Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block132Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block132HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block132Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block132Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block132Part000
    + surrogateDiagTailX0RatChunk000Sub001Block132Part001
    + surrogateDiagTailX0RatChunk000Sub001Block132Part002
    + surrogateDiagTailX0RatChunk000Sub001Block132Part003
    + surrogateDiagTailX0RatChunk000Sub001Block132Part004
    + surrogateDiagTailX0RatChunk000Sub001Block132Part005
    + surrogateDiagTailX0RatChunk000Sub001Block132Part006
    + surrogateDiagTailX0RatChunk000Sub001Block132Part007
    + surrogateDiagTailX0RatChunk000Sub001Block132Part008
    + surrogateDiagTailX0RatChunk000Sub001Block132Part009

def surrogateDiagonalTailChunk000Sub001Block132MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block132Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block132Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block132Part010
    + surrogateDiagTailX0RatChunk000Sub001Block132Part011
    + surrogateDiagTailX0RatChunk000Sub001Block132Part012
    + surrogateDiagTailX0RatChunk000Sub001Block132Part013
    + surrogateDiagTailX0RatChunk000Sub001Block132Part014
    + surrogateDiagTailX0RatChunk000Sub001Block132Part015
    + surrogateDiagTailX0RatChunk000Sub001Block132Part016
    + surrogateDiagTailX0RatChunk000Sub001Block132Part017
    + surrogateDiagTailX0RatChunk000Sub001Block132Part018
    + surrogateDiagTailX0RatChunk000Sub001Block132Part019

def surrogateDiagonalTailChunk000Sub001Block132TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block132Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block132Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block132Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block132Part020
    + surrogateDiagTailX0RatChunk000Sub001Block132Part021
    + surrogateDiagTailX0RatChunk000Sub001Block132Part022
    + surrogateDiagTailX0RatChunk000Sub001Block132Part023
    + surrogateDiagTailX0RatChunk000Sub001Block132Part024

def surrogateDiagonalTailChunk000Sub001Block132Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block132HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block132MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block132TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block132 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block132Part000
    + surrogateDiagTailX0RatChunk000Sub001Block132Part001
    + surrogateDiagTailX0RatChunk000Sub001Block132Part002
    + surrogateDiagTailX0RatChunk000Sub001Block132Part003
    + surrogateDiagTailX0RatChunk000Sub001Block132Part004
    + surrogateDiagTailX0RatChunk000Sub001Block132Part005
    + surrogateDiagTailX0RatChunk000Sub001Block132Part006
    + surrogateDiagTailX0RatChunk000Sub001Block132Part007
    + surrogateDiagTailX0RatChunk000Sub001Block132Part008
    + surrogateDiagTailX0RatChunk000Sub001Block132Part009
    + surrogateDiagTailX0RatChunk000Sub001Block132Part010
    + surrogateDiagTailX0RatChunk000Sub001Block132Part011
    + surrogateDiagTailX0RatChunk000Sub001Block132Part012
    + surrogateDiagTailX0RatChunk000Sub001Block132Part013
    + surrogateDiagTailX0RatChunk000Sub001Block132Part014
    + surrogateDiagTailX0RatChunk000Sub001Block132Part015
    + surrogateDiagTailX0RatChunk000Sub001Block132Part016
    + surrogateDiagTailX0RatChunk000Sub001Block132Part017
    + surrogateDiagTailX0RatChunk000Sub001Block132Part018
    + surrogateDiagTailX0RatChunk000Sub001Block132Part019
    + surrogateDiagTailX0RatChunk000Sub001Block132Part020
    + surrogateDiagTailX0RatChunk000Sub001Block132Part021
    + surrogateDiagTailX0RatChunk000Sub001Block132Part022
    + surrogateDiagTailX0RatChunk000Sub001Block132Part023
    + surrogateDiagTailX0RatChunk000Sub001Block132Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block132_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block132Head + surrogateDiagTailX0RatChunk000Sub001Block132Mid + surrogateDiagTailX0RatChunk000Sub001Block132Tail =
      surrogateDiagTailX0RatChunk000Sub001Block132 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block132Head surrogateDiagTailX0RatChunk000Sub001Block132Mid surrogateDiagTailX0RatChunk000Sub001Block132Tail surrogateDiagTailX0RatChunk000Sub001Block132
  ring

def SurrogateDiagonalTailChunk000Sub001Block132HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block132HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block132Head

def SurrogateDiagonalTailChunk000Sub001Block132MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block132MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block132Mid

def SurrogateDiagonalTailChunk000Sub001Block132TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block132TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block132Tail

theorem surrogateDiagonalTailChunk000Sub001Block132_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block132HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block132MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block132TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block132Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block132 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block132HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block132MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block132TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block132Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block132_eq_head_add_mid_add_tail

/-- Block 133 covers tail-support indices [8325,8350) and q from 13747 to 13790. -/

def TailChunk000Sub001Block133Part000SupportExplicit : Finset ℕ :=
  ([13747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part000 : ℚ :=
  (91873317025 : ℚ) / 81976764373990146048

def SurrogateDiagonalTailChunk000Sub001Block133Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13747
    = surrogateDiagTailX0RatChunk000Sub001Block133Part000

theorem surrogateDiagonalTailChunk000Sub001Block133Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part000] using hcert

def TailChunk000Sub001Block133Part001SupportExplicit : Finset ℕ :=
  ([13749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part001 : ℚ :=
  (656397661475 : ℚ) / 8817331830466864704

def SurrogateDiagonalTailChunk000Sub001Block133Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13749
    = surrogateDiagTailX0RatChunk000Sub001Block133Part001

theorem surrogateDiagonalTailChunk000Sub001Block133Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part001] using hcert

def TailChunk000Sub001Block133Part002SupportExplicit : Finset ℕ :=
  ([13751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block133Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13751
    = surrogateDiagTailX0RatChunk000Sub001Block133Part002

theorem surrogateDiagonalTailChunk000Sub001Block133Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part002] using hcert

def TailChunk000Sub001Block133Part003SupportExplicit : Finset ℕ :=
  ([13753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part003 : ℚ :=
  (41596270725 : ℚ) / 11641286622590271488

def SurrogateDiagonalTailChunk000Sub001Block133Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13753
    = surrogateDiagTailX0RatChunk000Sub001Block133Part003

theorem surrogateDiagonalTailChunk000Sub001Block133Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part003] using hcert

def TailChunk000Sub001Block133Part004SupportExplicit : Finset ℕ :=
  ([13755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part004 : ℚ :=
  (1866972053 : ℚ) / 5616444152217600

def SurrogateDiagonalTailChunk000Sub001Block133Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13755
    = surrogateDiagTailX0RatChunk000Sub001Block133Part004

theorem surrogateDiagonalTailChunk000Sub001Block133Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part004] using hcert

def TailChunk000Sub001Block133Part005SupportExplicit : Finset ℕ :=
  ([13757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block133Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13757
    = surrogateDiagTailX0RatChunk000Sub001Block133Part005

theorem surrogateDiagonalTailChunk000Sub001Block133Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part005] using hcert

def TailChunk000Sub001Block133Part006SupportExplicit : Finset ℕ :=
  ([13758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part006 : ℚ :=
  (821266271675 : ℚ) / 552046040204534784

def SurrogateDiagonalTailChunk000Sub001Block133Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13758
    = surrogateDiagTailX0RatChunk000Sub001Block133Part006

theorem surrogateDiagonalTailChunk000Sub001Block133Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part006] using hcert

def TailChunk000Sub001Block133Part007SupportExplicit : Finset ℕ :=
  ([13759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block133Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13759
    = surrogateDiagTailX0RatChunk000Sub001Block133Part007

theorem surrogateDiagonalTailChunk000Sub001Block133Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part007] using hcert

def TailChunk000Sub001Block133Part008SupportExplicit : Finset ℕ :=
  ([13762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part008 : ℚ :=
  (2413116011875 : ℚ) / 3013545906065720448

def SurrogateDiagonalTailChunk000Sub001Block133Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13762
    = surrogateDiagTailX0RatChunk000Sub001Block133Part008

theorem surrogateDiagonalTailChunk000Sub001Block133Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part008] using hcert

def TailChunk000Sub001Block133Part009SupportExplicit : Finset ℕ :=
  ([13763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block133Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13763
    = surrogateDiagTailX0RatChunk000Sub001Block133Part009

theorem surrogateDiagonalTailChunk000Sub001Block133Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part009] using hcert

def TailChunk000Sub001Block133Part010SupportExplicit : Finset ℕ :=
  ([13765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part010 : ℚ :=
  (947748961525 : ℚ) / 36716438035573506048

def SurrogateDiagonalTailChunk000Sub001Block133Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13765
    = surrogateDiagTailX0RatChunk000Sub001Block133Part010

theorem surrogateDiagonalTailChunk000Sub001Block133Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part010] using hcert

def TailChunk000Sub001Block133Part011SupportExplicit : Finset ℕ :=
  ([13766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part011 : ℚ :=
  (740245140625 : ℚ) / 1402250297094232722

def SurrogateDiagonalTailChunk000Sub001Block133Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13766
    = surrogateDiagTailX0RatChunk000Sub001Block133Part011

theorem surrogateDiagonalTailChunk000Sub001Block133Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part011] using hcert

def TailChunk000Sub001Block133Part012SupportExplicit : Finset ℕ :=
  ([13767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part012 : ℚ :=
  (605799212575 : ℚ) / 3184069130638589952

def SurrogateDiagonalTailChunk000Sub001Block133Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13767
    = surrogateDiagTailX0RatChunk000Sub001Block133Part012

theorem surrogateDiagonalTailChunk000Sub001Block133Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part012] using hcert

def TailChunk000Sub001Block133Part013SupportExplicit : Finset ℕ :=
  ([13771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part013 : ℚ :=
  (34876530075 : ℚ) / 27131158385025488896

def SurrogateDiagonalTailChunk000Sub001Block133Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13771
    = surrogateDiagTailX0RatChunk000Sub001Block133Part013

theorem surrogateDiagonalTailChunk000Sub001Block133Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part013] using hcert

def TailChunk000Sub001Block133Part014SupportExplicit : Finset ℕ :=
  ([13773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part014 : ℚ :=
  (5269525291 : ℚ) / 71032577692403520

def SurrogateDiagonalTailChunk000Sub001Block133Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13773
    = surrogateDiagTailX0RatChunk000Sub001Block133Part014

theorem surrogateDiagonalTailChunk000Sub001Block133Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part014] using hcert

def TailChunk000Sub001Block133Part015SupportExplicit : Finset ℕ :=
  ([13774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part015 : ℚ :=
  (1436871497 : ℚ) / 2549611183472640

def SurrogateDiagonalTailChunk000Sub001Block133Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13774
    = surrogateDiagTailX0RatChunk000Sub001Block133Part015

theorem surrogateDiagonalTailChunk000Sub001Block133Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part015] using hcert

def TailChunk000Sub001Block133Part016SupportExplicit : Finset ℕ :=
  ([13777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part016 : ℚ :=
  (207694600975 : ℚ) / 74906985176037176448

def SurrogateDiagonalTailChunk000Sub001Block133Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13777
    = surrogateDiagTailX0RatChunk000Sub001Block133Part016

theorem surrogateDiagonalTailChunk000Sub001Block133Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part016] using hcert

def TailChunk000Sub001Block133Part017SupportExplicit : Finset ℕ :=
  ([13781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block133Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13781
    = surrogateDiagTailX0RatChunk000Sub001Block133Part017

theorem surrogateDiagonalTailChunk000Sub001Block133Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part017] using hcert

def TailChunk000Sub001Block133Part018SupportExplicit : Finset ℕ :=
  ([13782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part018 : ℚ :=
  (824134230425 : ℚ) / 555909864770125824

def SurrogateDiagonalTailChunk000Sub001Block133Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13782
    = surrogateDiagTailX0RatChunk000Sub001Block133Part018

theorem surrogateDiagonalTailChunk000Sub001Block133Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part018] using hcert

def TailChunk000Sub001Block133Part019SupportExplicit : Finset ℕ :=
  ([13783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part019 : ℚ :=
  (2087344021 : ℚ) / 72293517444326400

def SurrogateDiagonalTailChunk000Sub001Block133Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13783
    = surrogateDiagTailX0RatChunk000Sub001Block133Part019

theorem surrogateDiagonalTailChunk000Sub001Block133Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part019] using hcert

def TailChunk000Sub001Block133Part020SupportExplicit : Finset ℕ :=
  ([13785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part020 : ℚ :=
  (171477588725 : ℚ) / 909216994462765056

def SurrogateDiagonalTailChunk000Sub001Block133Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13785
    = surrogateDiagTailX0RatChunk000Sub001Block133Part020

theorem surrogateDiagonalTailChunk000Sub001Block133Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part020] using hcert

def TailChunk000Sub001Block133Part021SupportExplicit : Finset ℕ :=
  ([13786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part021 : ℚ :=
  (115038398281 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block133Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13786
    = surrogateDiagTailX0RatChunk000Sub001Block133Part021

theorem surrogateDiagonalTailChunk000Sub001Block133Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part021] using hcert

def TailChunk000Sub001Block133Part022SupportExplicit : Finset ℕ :=
  ([13787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part022 : ℚ :=
  (557310911 : ℚ) / 156759673857638400

def SurrogateDiagonalTailChunk000Sub001Block133Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13787
    = surrogateDiagTailX0RatChunk000Sub001Block133Part022

theorem surrogateDiagonalTailChunk000Sub001Block133Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part022] using hcert

def TailChunk000Sub001Block133Part023SupportExplicit : Finset ℕ :=
  ([13789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block133Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13789
    = surrogateDiagTailX0RatChunk000Sub001Block133Part023

theorem surrogateDiagonalTailChunk000Sub001Block133Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part023] using hcert

def TailChunk000Sub001Block133Part024SupportExplicit : Finset ℕ :=
  ([13790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block133Part024 : ℚ :=
  (922283713625 : ℚ) / 612161645151780864

def SurrogateDiagonalTailChunk000Sub001Block133Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13790
    = surrogateDiagTailX0RatChunk000Sub001Block133Part024

theorem surrogateDiagonalTailChunk000Sub001Block133Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block133Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block133Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block133Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block133Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block133Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block133Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block133HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block133Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block133Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block133Part000
    + surrogateDiagTailX0RatChunk000Sub001Block133Part001
    + surrogateDiagTailX0RatChunk000Sub001Block133Part002
    + surrogateDiagTailX0RatChunk000Sub001Block133Part003
    + surrogateDiagTailX0RatChunk000Sub001Block133Part004
    + surrogateDiagTailX0RatChunk000Sub001Block133Part005
    + surrogateDiagTailX0RatChunk000Sub001Block133Part006
    + surrogateDiagTailX0RatChunk000Sub001Block133Part007
    + surrogateDiagTailX0RatChunk000Sub001Block133Part008
    + surrogateDiagTailX0RatChunk000Sub001Block133Part009

def surrogateDiagonalTailChunk000Sub001Block133MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block133Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block133Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block133Part010
    + surrogateDiagTailX0RatChunk000Sub001Block133Part011
    + surrogateDiagTailX0RatChunk000Sub001Block133Part012
    + surrogateDiagTailX0RatChunk000Sub001Block133Part013
    + surrogateDiagTailX0RatChunk000Sub001Block133Part014
    + surrogateDiagTailX0RatChunk000Sub001Block133Part015
    + surrogateDiagTailX0RatChunk000Sub001Block133Part016
    + surrogateDiagTailX0RatChunk000Sub001Block133Part017
    + surrogateDiagTailX0RatChunk000Sub001Block133Part018
    + surrogateDiagTailX0RatChunk000Sub001Block133Part019

def surrogateDiagonalTailChunk000Sub001Block133TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block133Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block133Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block133Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block133Part020
    + surrogateDiagTailX0RatChunk000Sub001Block133Part021
    + surrogateDiagTailX0RatChunk000Sub001Block133Part022
    + surrogateDiagTailX0RatChunk000Sub001Block133Part023
    + surrogateDiagTailX0RatChunk000Sub001Block133Part024

def surrogateDiagonalTailChunk000Sub001Block133Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block133HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block133MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block133TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block133 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block133Part000
    + surrogateDiagTailX0RatChunk000Sub001Block133Part001
    + surrogateDiagTailX0RatChunk000Sub001Block133Part002
    + surrogateDiagTailX0RatChunk000Sub001Block133Part003
    + surrogateDiagTailX0RatChunk000Sub001Block133Part004
    + surrogateDiagTailX0RatChunk000Sub001Block133Part005
    + surrogateDiagTailX0RatChunk000Sub001Block133Part006
    + surrogateDiagTailX0RatChunk000Sub001Block133Part007
    + surrogateDiagTailX0RatChunk000Sub001Block133Part008
    + surrogateDiagTailX0RatChunk000Sub001Block133Part009
    + surrogateDiagTailX0RatChunk000Sub001Block133Part010
    + surrogateDiagTailX0RatChunk000Sub001Block133Part011
    + surrogateDiagTailX0RatChunk000Sub001Block133Part012
    + surrogateDiagTailX0RatChunk000Sub001Block133Part013
    + surrogateDiagTailX0RatChunk000Sub001Block133Part014
    + surrogateDiagTailX0RatChunk000Sub001Block133Part015
    + surrogateDiagTailX0RatChunk000Sub001Block133Part016
    + surrogateDiagTailX0RatChunk000Sub001Block133Part017
    + surrogateDiagTailX0RatChunk000Sub001Block133Part018
    + surrogateDiagTailX0RatChunk000Sub001Block133Part019
    + surrogateDiagTailX0RatChunk000Sub001Block133Part020
    + surrogateDiagTailX0RatChunk000Sub001Block133Part021
    + surrogateDiagTailX0RatChunk000Sub001Block133Part022
    + surrogateDiagTailX0RatChunk000Sub001Block133Part023
    + surrogateDiagTailX0RatChunk000Sub001Block133Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block133_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block133Head + surrogateDiagTailX0RatChunk000Sub001Block133Mid + surrogateDiagTailX0RatChunk000Sub001Block133Tail =
      surrogateDiagTailX0RatChunk000Sub001Block133 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block133Head surrogateDiagTailX0RatChunk000Sub001Block133Mid surrogateDiagTailX0RatChunk000Sub001Block133Tail surrogateDiagTailX0RatChunk000Sub001Block133
  ring

def SurrogateDiagonalTailChunk000Sub001Block133HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block133HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block133Head

def SurrogateDiagonalTailChunk000Sub001Block133MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block133MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block133Mid

def SurrogateDiagonalTailChunk000Sub001Block133TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block133TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block133Tail

theorem surrogateDiagonalTailChunk000Sub001Block133_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block133HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block133MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block133TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block133Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block133 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block133HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block133MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block133TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block133Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block133_eq_head_add_mid_add_tail

/-- Block 134 covers tail-support indices [8350,8375) and q from 13791 to 13831. -/

def TailChunk000Sub001Block134Part000SupportExplicit : Finset ℕ :=
  ([13791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part000 : ℚ :=
  (165103259075 : ℚ) / 2231397461167462656

def SurrogateDiagonalTailChunk000Sub001Block134Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13791
    = surrogateDiagTailX0RatChunk000Sub001Block134Part000

theorem surrogateDiagonalTailChunk000Sub001Block134Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part000] using hcert

def TailChunk000Sub001Block134Part001SupportExplicit : Finset ℕ :=
  ([13793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part001 : ℚ :=
  (1896564079 : ℚ) / 436399299783475200

def SurrogateDiagonalTailChunk000Sub001Block134Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13793
    = surrogateDiagTailX0RatChunk000Sub001Block134Part001

theorem surrogateDiagonalTailChunk000Sub001Block134Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part001] using hcert

def TailChunk000Sub001Block134Part002SupportExplicit : Finset ℕ :=
  ([13795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part002 : ℚ :=
  (1353992317 : ℚ) / 41459233471856640

def SurrogateDiagonalTailChunk000Sub001Block134Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13795
    = surrogateDiagTailX0RatChunk000Sub001Block134Part002

theorem surrogateDiagonalTailChunk000Sub001Block134Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part002] using hcert

def TailChunk000Sub001Block134Part003SupportExplicit : Finset ℕ :=
  ([13798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part003 : ℚ :=
  (743690640625 : ℚ) / 1415336242158312402

def SurrogateDiagonalTailChunk000Sub001Block134Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13798
    = surrogateDiagTailX0RatChunk000Sub001Block134Part003

theorem surrogateDiagonalTailChunk000Sub001Block134Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part003] using hcert

def TailChunk000Sub001Block134Part004SupportExplicit : Finset ℕ :=
  ([13799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block134Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13799
    = surrogateDiagTailX0RatChunk000Sub001Block134Part004

theorem surrogateDiagonalTailChunk000Sub001Block134Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part004] using hcert

def TailChunk000Sub001Block134Part005SupportExplicit : Finset ℕ :=
  ([13801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part005 : ℚ :=
  (61703432225 : ℚ) / 40214125211300020224

def SurrogateDiagonalTailChunk000Sub001Block134Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13801
    = surrogateDiagTailX0RatChunk000Sub001Block134Part005

theorem surrogateDiagonalTailChunk000Sub001Block134Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part005] using hcert

def TailChunk000Sub001Block134Part006SupportExplicit : Finset ℕ :=
  ([13802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part006 : ℚ :=
  (2884032181825 : ℚ) / 5135743061701135488

def SurrogateDiagonalTailChunk000Sub001Block134Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13802
    = surrogateDiagTailX0RatChunk000Sub001Block134Part006

theorem surrogateDiagonalTailChunk000Sub001Block134Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part006] using hcert

def TailChunk000Sub001Block134Part007SupportExplicit : Finset ℕ :=
  ([13803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part007 : ℚ :=
  (190151789125 : ℚ) / 2245274397385979904

def SurrogateDiagonalTailChunk000Sub001Block134Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13803
    = surrogateDiagTailX0RatChunk000Sub001Block134Part007

theorem surrogateDiagonalTailChunk000Sub001Block134Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part007] using hcert

def TailChunk000Sub001Block134Part008SupportExplicit : Finset ℕ :=
  ([13805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part008 : ℚ :=
  (28313683477 : ℚ) / 1000200000000000000

def SurrogateDiagonalTailChunk000Sub001Block134Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13805
    = surrogateDiagTailX0RatChunk000Sub001Block134Part008

theorem surrogateDiagonalTailChunk000Sub001Block134Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part008] using hcert

def TailChunk000Sub001Block134Part009SupportExplicit : Finset ℕ :=
  ([13807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block134Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13807
    = surrogateDiagTailX0RatChunk000Sub001Block134Part009

theorem surrogateDiagonalTailChunk000Sub001Block134Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part009] using hcert

def TailChunk000Sub001Block134Part010SupportExplicit : Finset ℕ :=
  ([13809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part010 : ℚ :=
  (662137661225 : ℚ) / 8972290018928268864

def SurrogateDiagonalTailChunk000Sub001Block134Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13809
    = surrogateDiagTailX0RatChunk000Sub001Block134Part010

theorem surrogateDiagonalTailChunk000Sub001Block134Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part010] using hcert

def TailChunk000Sub001Block134Part011SupportExplicit : Finset ℕ :=
  ([13810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part011 : ℚ :=
  (85761341317 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk000Sub001Block134Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13810
    = surrogateDiagTailX0RatChunk000Sub001Block134Part011

theorem surrogateDiagonalTailChunk000Sub001Block134Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part011] using hcert

def TailChunk000Sub001Block134Part012SupportExplicit : Finset ℕ :=
  ([13811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part012 : ℚ :=
  (243937783175 : ℚ) / 24503578153506284544

def SurrogateDiagonalTailChunk000Sub001Block134Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13811
    = surrogateDiagTailX0RatChunk000Sub001Block134Part012

theorem surrogateDiagonalTailChunk000Sub001Block134Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part012] using hcert

def TailChunk000Sub001Block134Part013SupportExplicit : Finset ℕ :=
  ([13813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part013 : ℚ :=
  (26215690625 : ℚ) / 8102533823796373632

def SurrogateDiagonalTailChunk000Sub001Block134Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13813
    = surrogateDiagTailX0RatChunk000Sub001Block134Part013

theorem surrogateDiagonalTailChunk000Sub001Block134Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part013] using hcert

def TailChunk000Sub001Block134Part014SupportExplicit : Finset ℕ :=
  ([13814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part014 : ℚ :=
  (745416390625 : ℚ) / 1421913454402525362

def SurrogateDiagonalTailChunk000Sub001Block134Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13814
    = surrogateDiagTailX0RatChunk000Sub001Block134Part014

theorem surrogateDiagonalTailChunk000Sub001Block134Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part014] using hcert

def TailChunk000Sub001Block134Part015SupportExplicit : Finset ℕ :=
  ([13817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part015 : ℚ :=
  (73780081 : ℚ) / 50992223669452800

def SurrogateDiagonalTailChunk000Sub001Block134Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13817
    = surrogateDiagTailX0RatChunk000Sub001Block134Part015

theorem surrogateDiagonalTailChunk000Sub001Block134Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part015] using hcert

def TailChunk000Sub001Block134Part016SupportExplicit : Finset ℕ :=
  ([13819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part016 : ℚ :=
  (39546892375 : ℚ) / 7328370209781123072

def SurrogateDiagonalTailChunk000Sub001Block134Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13819
    = surrogateDiagTailX0RatChunk000Sub001Block134Part016

theorem surrogateDiagonalTailChunk000Sub001Block134Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part016] using hcert

def TailChunk000Sub001Block134Part017SupportExplicit : Finset ℕ :=
  ([13821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part017 : ℚ :=
  (53433952051 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk000Sub001Block134Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13821
    = surrogateDiagTailX0RatChunk000Sub001Block134Part017

theorem surrogateDiagonalTailChunk000Sub001Block134Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part017] using hcert

def TailChunk000Sub001Block134Part018SupportExplicit : Finset ℕ :=
  ([13822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part018 : ℚ :=
  (1194048025 : ℚ) / 2280337029820722

def SurrogateDiagonalTailChunk000Sub001Block134Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13822
    = surrogateDiagTailX0RatChunk000Sub001Block134Part018

theorem surrogateDiagonalTailChunk000Sub001Block134Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part018] using hcert

def TailChunk000Sub001Block134Part019SupportExplicit : Finset ℕ :=
  ([13823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part019 : ℚ :=
  (8361607801 : ℚ) / 3036564951552000000

def SurrogateDiagonalTailChunk000Sub001Block134Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13823
    = surrogateDiagTailX0RatChunk000Sub001Block134Part019

theorem surrogateDiagonalTailChunk000Sub001Block134Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part019] using hcert

def TailChunk000Sub001Block134Part020SupportExplicit : Finset ℕ :=
  ([13826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part020 : ℚ :=
  (113869193047 : ℚ) / 196781273521027200

def SurrogateDiagonalTailChunk000Sub001Block134Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13826
    = surrogateDiagTailX0RatChunk000Sub001Block134Part020

theorem surrogateDiagonalTailChunk000Sub001Block134Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part020] using hcert

def TailChunk000Sub001Block134Part021SupportExplicit : Finset ℕ :=
  ([13827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part021 : ℚ :=
  (112454007 : ℚ) / 1017819395707840

def SurrogateDiagonalTailChunk000Sub001Block134Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13827
    = surrogateDiagTailX0RatChunk000Sub001Block134Part021

theorem surrogateDiagonalTailChunk000Sub001Block134Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part021] using hcert

def TailChunk000Sub001Block134Part022SupportExplicit : Finset ℕ :=
  ([13829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block134Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13829
    = surrogateDiagTailX0RatChunk000Sub001Block134Part022

theorem surrogateDiagonalTailChunk000Sub001Block134Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part022] using hcert

def TailChunk000Sub001Block134Part023SupportExplicit : Finset ℕ :=
  ([13830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part023 : ℚ :=
  (3743037259 : ℚ) / 1146457981747200

def SurrogateDiagonalTailChunk000Sub001Block134Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13830
    = surrogateDiagTailX0RatChunk000Sub001Block134Part023

theorem surrogateDiagonalTailChunk000Sub001Block134Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part023] using hcert

def TailChunk000Sub001Block134Part024SupportExplicit : Finset ℕ :=
  ([13831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block134Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block134Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13831
    = surrogateDiagTailX0RatChunk000Sub001Block134Part024

theorem surrogateDiagonalTailChunk000Sub001Block134Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block134Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block134Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block134Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block134Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block134Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block134Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block134HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block134Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block134Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block134Part000
    + surrogateDiagTailX0RatChunk000Sub001Block134Part001
    + surrogateDiagTailX0RatChunk000Sub001Block134Part002
    + surrogateDiagTailX0RatChunk000Sub001Block134Part003
    + surrogateDiagTailX0RatChunk000Sub001Block134Part004
    + surrogateDiagTailX0RatChunk000Sub001Block134Part005
    + surrogateDiagTailX0RatChunk000Sub001Block134Part006
    + surrogateDiagTailX0RatChunk000Sub001Block134Part007
    + surrogateDiagTailX0RatChunk000Sub001Block134Part008
    + surrogateDiagTailX0RatChunk000Sub001Block134Part009

def surrogateDiagonalTailChunk000Sub001Block134MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block134Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block134Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block134Part010
    + surrogateDiagTailX0RatChunk000Sub001Block134Part011
    + surrogateDiagTailX0RatChunk000Sub001Block134Part012
    + surrogateDiagTailX0RatChunk000Sub001Block134Part013
    + surrogateDiagTailX0RatChunk000Sub001Block134Part014
    + surrogateDiagTailX0RatChunk000Sub001Block134Part015
    + surrogateDiagTailX0RatChunk000Sub001Block134Part016
    + surrogateDiagTailX0RatChunk000Sub001Block134Part017
    + surrogateDiagTailX0RatChunk000Sub001Block134Part018
    + surrogateDiagTailX0RatChunk000Sub001Block134Part019

def surrogateDiagonalTailChunk000Sub001Block134TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block134Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block134Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block134Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block134Part020
    + surrogateDiagTailX0RatChunk000Sub001Block134Part021
    + surrogateDiagTailX0RatChunk000Sub001Block134Part022
    + surrogateDiagTailX0RatChunk000Sub001Block134Part023
    + surrogateDiagTailX0RatChunk000Sub001Block134Part024

def surrogateDiagonalTailChunk000Sub001Block134Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block134HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block134MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block134TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block134 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block134Part000
    + surrogateDiagTailX0RatChunk000Sub001Block134Part001
    + surrogateDiagTailX0RatChunk000Sub001Block134Part002
    + surrogateDiagTailX0RatChunk000Sub001Block134Part003
    + surrogateDiagTailX0RatChunk000Sub001Block134Part004
    + surrogateDiagTailX0RatChunk000Sub001Block134Part005
    + surrogateDiagTailX0RatChunk000Sub001Block134Part006
    + surrogateDiagTailX0RatChunk000Sub001Block134Part007
    + surrogateDiagTailX0RatChunk000Sub001Block134Part008
    + surrogateDiagTailX0RatChunk000Sub001Block134Part009
    + surrogateDiagTailX0RatChunk000Sub001Block134Part010
    + surrogateDiagTailX0RatChunk000Sub001Block134Part011
    + surrogateDiagTailX0RatChunk000Sub001Block134Part012
    + surrogateDiagTailX0RatChunk000Sub001Block134Part013
    + surrogateDiagTailX0RatChunk000Sub001Block134Part014
    + surrogateDiagTailX0RatChunk000Sub001Block134Part015
    + surrogateDiagTailX0RatChunk000Sub001Block134Part016
    + surrogateDiagTailX0RatChunk000Sub001Block134Part017
    + surrogateDiagTailX0RatChunk000Sub001Block134Part018
    + surrogateDiagTailX0RatChunk000Sub001Block134Part019
    + surrogateDiagTailX0RatChunk000Sub001Block134Part020
    + surrogateDiagTailX0RatChunk000Sub001Block134Part021
    + surrogateDiagTailX0RatChunk000Sub001Block134Part022
    + surrogateDiagTailX0RatChunk000Sub001Block134Part023
    + surrogateDiagTailX0RatChunk000Sub001Block134Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block134_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block134Head + surrogateDiagTailX0RatChunk000Sub001Block134Mid + surrogateDiagTailX0RatChunk000Sub001Block134Tail =
      surrogateDiagTailX0RatChunk000Sub001Block134 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block134Head surrogateDiagTailX0RatChunk000Sub001Block134Mid surrogateDiagTailX0RatChunk000Sub001Block134Tail surrogateDiagTailX0RatChunk000Sub001Block134
  ring

def SurrogateDiagonalTailChunk000Sub001Block134HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block134HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block134Head

def SurrogateDiagonalTailChunk000Sub001Block134MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block134MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block134Mid

def SurrogateDiagonalTailChunk000Sub001Block134TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block134TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block134Tail

theorem surrogateDiagonalTailChunk000Sub001Block134_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block134HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block134MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block134TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block134Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block134 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block134HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block134MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block134TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block134Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block134_eq_head_add_mid_add_tail

/-- Block 135 covers tail-support indices [8375,8400) and q from 13834 to 13874. -/

def TailChunk000Sub001Block135Part000SupportExplicit : Finset ℕ :=
  ([13834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part000 : ℚ :=
  (747576390625 : ℚ) / 1430167175036719392

def SurrogateDiagonalTailChunk000Sub001Block135Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13834
    = surrogateDiagTailX0RatChunk000Sub001Block135Part000

theorem surrogateDiagonalTailChunk000Sub001Block135Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part000] using hcert

def TailChunk000Sub001Block135Part001SupportExplicit : Finset ℕ :=
  ([13835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part001 : ℚ :=
  (319134508675 : ℚ) / 12489765159468865536

def SurrogateDiagonalTailChunk000Sub001Block135Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13835
    = surrogateDiagTailX0RatChunk000Sub001Block135Part001

theorem surrogateDiagonalTailChunk000Sub001Block135Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part001] using hcert

def TailChunk000Sub001Block135Part002SupportExplicit : Finset ℕ :=
  ([13837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part002 : ℚ :=
  (986887557 : ℚ) / 1140568121344000000

def SurrogateDiagonalTailChunk000Sub001Block135Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13837
    = surrogateDiagTailX0RatChunk000Sub001Block135Part002

theorem surrogateDiagonalTailChunk000Sub001Block135Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part002] using hcert

def TailChunk000Sub001Block135Part003SupportExplicit : Finset ℕ :=
  ([13838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part003 : ℚ :=
  (238787599 : ℚ) / 2038839430348800

def SurrogateDiagonalTailChunk000Sub001Block135Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13838
    = surrogateDiagTailX0RatChunk000Sub001Block135Part003

theorem surrogateDiagonalTailChunk000Sub001Block135Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part003] using hcert

def TailChunk000Sub001Block135Part004SupportExplicit : Finset ℕ :=
  ([13839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part004 : ℚ :=
  (1410813375925 : ℚ) / 9719757226077308928

def SurrogateDiagonalTailChunk000Sub001Block135Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13839
    = surrogateDiagTailX0RatChunk000Sub001Block135Part004

theorem surrogateDiagonalTailChunk000Sub001Block135Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part004] using hcert

def TailChunk000Sub001Block135Part005SupportExplicit : Finset ℕ :=
  ([13841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block135Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13841
    = surrogateDiagTailX0RatChunk000Sub001Block135Part005

theorem surrogateDiagonalTailChunk000Sub001Block135Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part005] using hcert

def TailChunk000Sub001Block135Part006SupportExplicit : Finset ℕ :=
  ([13843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part006 : ℚ :=
  (5160374525 : ℚ) / 6124575963918892032

def SurrogateDiagonalTailChunk000Sub001Block135Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13843
    = surrogateDiagTailX0RatChunk000Sub001Block135Part006

theorem surrogateDiagonalTailChunk000Sub001Block135Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part006] using hcert

def TailChunk000Sub001Block135Part007SupportExplicit : Finset ℕ :=
  ([13845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part007 : ℚ :=
  (7929516337 : ℚ) / 29138413525401600

def SurrogateDiagonalTailChunk000Sub001Block135Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13845
    = surrogateDiagTailX0RatChunk000Sub001Block135Part007

theorem surrogateDiagonalTailChunk000Sub001Block135Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part007] using hcert

def TailChunk000Sub001Block135Part008SupportExplicit : Finset ℕ :=
  ([13846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part008 : ℚ :=
  (27262476575 : ℚ) / 168729768097938432

def SurrogateDiagonalTailChunk000Sub001Block135Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13846
    = surrogateDiagTailX0RatChunk000Sub001Block135Part008

theorem surrogateDiagonalTailChunk000Sub001Block135Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part008] using hcert

def TailChunk000Sub001Block135Part009SupportExplicit : Finset ℕ :=
  ([13847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part009 : ℚ :=
  (295638281 : ℚ) / 281802188975961600

def SurrogateDiagonalTailChunk000Sub001Block135Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13847
    = surrogateDiagTailX0RatChunk000Sub001Block135Part009

theorem surrogateDiagonalTailChunk000Sub001Block135Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part009] using hcert

def TailChunk000Sub001Block135Part010SupportExplicit : Finset ℕ :=
  ([13849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part010 : ℚ :=
  (5313744783 : ℚ) / 835003238619606400

def SurrogateDiagonalTailChunk000Sub001Block135Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13849
    = surrogateDiagTailX0RatChunk000Sub001Block135Part010

theorem surrogateDiagonalTailChunk000Sub001Block135Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part010] using hcert

def TailChunk000Sub001Block135Part011SupportExplicit : Finset ℕ :=
  ([13853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part011 : ℚ :=
  (40842885475 : ℚ) / 2755906660163889216

def SurrogateDiagonalTailChunk000Sub001Block135Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13853
    = surrogateDiagTailX0RatChunk000Sub001Block135Part011

theorem surrogateDiagonalTailChunk000Sub001Block135Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part011] using hcert

def TailChunk000Sub001Block135Part012SupportExplicit : Finset ℕ :=
  ([13854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part012 : ℚ :=
  (333174861275 : ℚ) / 567623103410217984

def SurrogateDiagonalTailChunk000Sub001Block135Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13854
    = surrogateDiagTailX0RatChunk000Sub001Block135Part012

theorem surrogateDiagonalTailChunk000Sub001Block135Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part012] using hcert

def TailChunk000Sub001Block135Part013SupportExplicit : Finset ℕ :=
  ([13855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part013 : ℚ :=
  (1054847204125 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk000Sub001Block135Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13855
    = surrogateDiagTailX0RatChunk000Sub001Block135Part013

theorem surrogateDiagonalTailChunk000Sub001Block135Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part013] using hcert

def TailChunk000Sub001Block135Part014SupportExplicit : Finset ℕ :=
  ([13857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part014 : ℚ :=
  (26823646169 : ℚ) / 310963000131993600

def SurrogateDiagonalTailChunk000Sub001Block135Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13857
    = surrogateDiagTailX0RatChunk000Sub001Block135Part014

theorem surrogateDiagonalTailChunk000Sub001Block135Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part014] using hcert

def TailChunk000Sub001Block135Part015SupportExplicit : Finset ℕ :=
  ([13859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block135Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13859
    = surrogateDiagTailX0RatChunk000Sub001Block135Part015

theorem surrogateDiagonalTailChunk000Sub001Block135Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part015] using hcert

def TailChunk000Sub001Block135Part016SupportExplicit : Finset ℕ :=
  ([13861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part016 : ℚ :=
  (9398962175 : ℚ) / 10730615502544196496

def SurrogateDiagonalTailChunk000Sub001Block135Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13861
    = surrogateDiagTailX0RatChunk000Sub001Block135Part016

theorem surrogateDiagonalTailChunk000Sub001Block135Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part016] using hcert

def TailChunk000Sub001Block135Part017SupportExplicit : Finset ℕ :=
  ([13862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part017 : ℚ :=
  (235908975 : ℚ) / 14676670193062528

def SurrogateDiagonalTailChunk000Sub001Block135Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13862
    = surrogateDiagTailX0RatChunk000Sub001Block135Part017

theorem surrogateDiagonalTailChunk000Sub001Block135Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part017] using hcert

def TailChunk000Sub001Block135Part018SupportExplicit : Finset ℕ :=
  ([13863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part018 : ℚ :=
  (23833037 : ℚ) / 325481805744480

def SurrogateDiagonalTailChunk000Sub001Block135Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13863
    = surrogateDiagTailX0RatChunk000Sub001Block135Part018

theorem surrogateDiagonalTailChunk000Sub001Block135Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part018] using hcert

def TailChunk000Sub001Block135Part019SupportExplicit : Finset ℕ :=
  ([13865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part019 : ℚ :=
  (508642433225 : ℚ) / 16217358955762827264

def SurrogateDiagonalTailChunk000Sub001Block135Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13865
    = surrogateDiagTailX0RatChunk000Sub001Block135Part019

theorem surrogateDiagonalTailChunk000Sub001Block135Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part019] using hcert

def TailChunk000Sub001Block135Part020SupportExplicit : Finset ℕ :=
  ([13866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part020 : ℚ :=
  (13350079829 : ℚ) / 22783726402113600

def SurrogateDiagonalTailChunk000Sub001Block135Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13866
    = surrogateDiagTailX0RatChunk000Sub001Block135Part020

theorem surrogateDiagonalTailChunk000Sub001Block135Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part020] using hcert

def TailChunk000Sub001Block135Part021SupportExplicit : Finset ℕ :=
  ([13870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part021 : ℚ :=
  (530597981575 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub001Block135Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13870
    = surrogateDiagTailX0RatChunk000Sub001Block135Part021

theorem surrogateDiagonalTailChunk000Sub001Block135Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part021] using hcert

def TailChunk000Sub001Block135Part022SupportExplicit : Finset ℕ :=
  ([13871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part022 : ℚ :=
  (909056627 : ℚ) / 58718575594045440

def SurrogateDiagonalTailChunk000Sub001Block135Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13871
    = surrogateDiagTailX0RatChunk000Sub001Block135Part022

theorem surrogateDiagonalTailChunk000Sub001Block135Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part022] using hcert

def TailChunk000Sub001Block135Part023SupportExplicit : Finset ℕ :=
  ([13873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block135Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13873
    = surrogateDiagTailX0RatChunk000Sub001Block135Part023

theorem surrogateDiagonalTailChunk000Sub001Block135Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part023] using hcert

def TailChunk000Sub001Block135Part024SupportExplicit : Finset ℕ :=
  ([13874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block135Part024 : ℚ :=
  (12316419091 : ℚ) / 124518141544579200

def SurrogateDiagonalTailChunk000Sub001Block135Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13874
    = surrogateDiagTailX0RatChunk000Sub001Block135Part024

theorem surrogateDiagonalTailChunk000Sub001Block135Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block135Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block135Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block135Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block135Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block135Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block135Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block135HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block135Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block135Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block135Part000
    + surrogateDiagTailX0RatChunk000Sub001Block135Part001
    + surrogateDiagTailX0RatChunk000Sub001Block135Part002
    + surrogateDiagTailX0RatChunk000Sub001Block135Part003
    + surrogateDiagTailX0RatChunk000Sub001Block135Part004
    + surrogateDiagTailX0RatChunk000Sub001Block135Part005
    + surrogateDiagTailX0RatChunk000Sub001Block135Part006
    + surrogateDiagTailX0RatChunk000Sub001Block135Part007
    + surrogateDiagTailX0RatChunk000Sub001Block135Part008
    + surrogateDiagTailX0RatChunk000Sub001Block135Part009

def surrogateDiagonalTailChunk000Sub001Block135MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block135Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block135Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block135Part010
    + surrogateDiagTailX0RatChunk000Sub001Block135Part011
    + surrogateDiagTailX0RatChunk000Sub001Block135Part012
    + surrogateDiagTailX0RatChunk000Sub001Block135Part013
    + surrogateDiagTailX0RatChunk000Sub001Block135Part014
    + surrogateDiagTailX0RatChunk000Sub001Block135Part015
    + surrogateDiagTailX0RatChunk000Sub001Block135Part016
    + surrogateDiagTailX0RatChunk000Sub001Block135Part017
    + surrogateDiagTailX0RatChunk000Sub001Block135Part018
    + surrogateDiagTailX0RatChunk000Sub001Block135Part019

def surrogateDiagonalTailChunk000Sub001Block135TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block135Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block135Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block135Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block135Part020
    + surrogateDiagTailX0RatChunk000Sub001Block135Part021
    + surrogateDiagTailX0RatChunk000Sub001Block135Part022
    + surrogateDiagTailX0RatChunk000Sub001Block135Part023
    + surrogateDiagTailX0RatChunk000Sub001Block135Part024

def surrogateDiagonalTailChunk000Sub001Block135Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block135HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block135MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block135TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block135 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block135Part000
    + surrogateDiagTailX0RatChunk000Sub001Block135Part001
    + surrogateDiagTailX0RatChunk000Sub001Block135Part002
    + surrogateDiagTailX0RatChunk000Sub001Block135Part003
    + surrogateDiagTailX0RatChunk000Sub001Block135Part004
    + surrogateDiagTailX0RatChunk000Sub001Block135Part005
    + surrogateDiagTailX0RatChunk000Sub001Block135Part006
    + surrogateDiagTailX0RatChunk000Sub001Block135Part007
    + surrogateDiagTailX0RatChunk000Sub001Block135Part008
    + surrogateDiagTailX0RatChunk000Sub001Block135Part009
    + surrogateDiagTailX0RatChunk000Sub001Block135Part010
    + surrogateDiagTailX0RatChunk000Sub001Block135Part011
    + surrogateDiagTailX0RatChunk000Sub001Block135Part012
    + surrogateDiagTailX0RatChunk000Sub001Block135Part013
    + surrogateDiagTailX0RatChunk000Sub001Block135Part014
    + surrogateDiagTailX0RatChunk000Sub001Block135Part015
    + surrogateDiagTailX0RatChunk000Sub001Block135Part016
    + surrogateDiagTailX0RatChunk000Sub001Block135Part017
    + surrogateDiagTailX0RatChunk000Sub001Block135Part018
    + surrogateDiagTailX0RatChunk000Sub001Block135Part019
    + surrogateDiagTailX0RatChunk000Sub001Block135Part020
    + surrogateDiagTailX0RatChunk000Sub001Block135Part021
    + surrogateDiagTailX0RatChunk000Sub001Block135Part022
    + surrogateDiagTailX0RatChunk000Sub001Block135Part023
    + surrogateDiagTailX0RatChunk000Sub001Block135Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block135_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block135Head + surrogateDiagTailX0RatChunk000Sub001Block135Mid + surrogateDiagTailX0RatChunk000Sub001Block135Tail =
      surrogateDiagTailX0RatChunk000Sub001Block135 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block135Head surrogateDiagTailX0RatChunk000Sub001Block135Mid surrogateDiagTailX0RatChunk000Sub001Block135Tail surrogateDiagTailX0RatChunk000Sub001Block135
  ring

def SurrogateDiagonalTailChunk000Sub001Block135HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block135HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block135Head

def SurrogateDiagonalTailChunk000Sub001Block135MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block135MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block135Mid

def SurrogateDiagonalTailChunk000Sub001Block135TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block135TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block135Tail

theorem surrogateDiagonalTailChunk000Sub001Block135_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block135HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block135MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block135TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block135Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block135 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block135HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block135MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block135TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block135Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block135_eq_head_add_mid_add_tail

/-- Block 136 covers tail-support indices [8400,8425) and q from 13877 to 13913. -/

def TailChunk000Sub001Block136Part000SupportExplicit : Finset ℕ :=
  ([13877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block136Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13877
    = surrogateDiagTailX0RatChunk000Sub001Block136Part000

theorem surrogateDiagonalTailChunk000Sub001Block136Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part000] using hcert

def TailChunk000Sub001Block136Part001SupportExplicit : Finset ℕ :=
  ([13879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block136Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13879
    = surrogateDiagTailX0RatChunk000Sub001Block136Part001

theorem surrogateDiagonalTailChunk000Sub001Block136Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part001] using hcert

def TailChunk000Sub001Block136Part002SupportExplicit : Finset ℕ :=
  ([13881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part002 : ℚ :=
  (5824939421 : ℚ) / 43726535302348800

def SurrogateDiagonalTailChunk000Sub001Block136Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13881
    = surrogateDiagTailX0RatChunk000Sub001Block136Part002

theorem surrogateDiagonalTailChunk000Sub001Block136Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part002] using hcert

def TailChunk000Sub001Block136Part003SupportExplicit : Finset ℕ :=
  ([13882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part003 : ℚ :=
  (2683982089 : ℚ) / 52520371974000000

def SurrogateDiagonalTailChunk000Sub001Block136Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13882
    = surrogateDiagTailX0RatChunk000Sub001Block136Part003

theorem surrogateDiagonalTailChunk000Sub001Block136Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part003] using hcert

def TailChunk000Sub001Block136Part004SupportExplicit : Finset ℕ :=
  ([13883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block136Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13883
    = surrogateDiagTailX0RatChunk000Sub001Block136Part004

theorem surrogateDiagonalTailChunk000Sub001Block136Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part004] using hcert

def TailChunk000Sub001Block136Part005SupportExplicit : Finset ℕ :=
  ([13885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part005 : ℚ :=
  (160962280125 : ℚ) / 12671365455506046976

def SurrogateDiagonalTailChunk000Sub001Block136Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13885
    = surrogateDiagTailX0RatChunk000Sub001Block136Part005

theorem surrogateDiagonalTailChunk000Sub001Block136Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part005] using hcert

def TailChunk000Sub001Block136Part006SupportExplicit : Finset ℕ :=
  ([13886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part006 : ℚ :=
  (1123880951 : ℚ) / 104434414994457600

def SurrogateDiagonalTailChunk000Sub001Block136Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13886
    = surrogateDiagTailX0RatChunk000Sub001Block136Part006

theorem surrogateDiagonalTailChunk000Sub001Block136Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part006] using hcert

def TailChunk000Sub001Block136Part007SupportExplicit : Finset ℕ :=
  ([13889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part007 : ℚ :=
  (4814059897025 : ℚ) / 26764798359622385664

def SurrogateDiagonalTailChunk000Sub001Block136Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13889
    = surrogateDiagTailX0RatChunk000Sub001Block136Part007

theorem surrogateDiagonalTailChunk000Sub001Block136Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part007] using hcert

def TailChunk000Sub001Block136Part008SupportExplicit : Finset ℕ :=
  ([13890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part008 : ℚ :=
  (251706789275 : ℚ) / 77768452785881088

def SurrogateDiagonalTailChunk000Sub001Block136Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13890
    = surrogateDiagTailX0RatChunk000Sub001Block136Part008

theorem surrogateDiagonalTailChunk000Sub001Block136Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part008] using hcert

def TailChunk000Sub001Block136Part009SupportExplicit : Finset ℕ :=
  ([13891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part009 : ℚ :=
  (11348536086925 : ℚ) / 80236240360964179968

def SurrogateDiagonalTailChunk000Sub001Block136Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13891
    = surrogateDiagTailX0RatChunk000Sub001Block136Part009

theorem surrogateDiagonalTailChunk000Sub001Block136Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part009] using hcert

def TailChunk000Sub001Block136Part010SupportExplicit : Finset ℕ :=
  ([13893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part010 : ℚ :=
  (707294239 : ℚ) / 1536947328000000

def SurrogateDiagonalTailChunk000Sub001Block136Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13893
    = surrogateDiagTailX0RatChunk000Sub001Block136Part010

theorem surrogateDiagonalTailChunk000Sub001Block136Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part010] using hcert

def TailChunk000Sub001Block136Part011SupportExplicit : Finset ℕ :=
  ([13894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part011 : ℚ :=
  (754075140625 : ℚ) / 1455144035307348882

def SurrogateDiagonalTailChunk000Sub001Block136Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13894
    = surrogateDiagTailX0RatChunk000Sub001Block136Part011

theorem surrogateDiagonalTailChunk000Sub001Block136Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part011] using hcert

def TailChunk000Sub001Block136Part012SupportExplicit : Finset ℕ :=
  ([13895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part012 : ℚ :=
  (3204044054225 : ℚ) / 10200526155331928064

def SurrogateDiagonalTailChunk000Sub001Block136Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13895
    = surrogateDiagTailX0RatChunk000Sub001Block136Part012

theorem surrogateDiagonalTailChunk000Sub001Block136Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part012] using hcert

def TailChunk000Sub001Block136Part013SupportExplicit : Finset ℕ :=
  ([13897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part013 : ℚ :=
  (5277856899725 : ℚ) / 33729263498824925184

def SurrogateDiagonalTailChunk000Sub001Block136Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13897
    = surrogateDiagTailX0RatChunk000Sub001Block136Part013

theorem surrogateDiagonalTailChunk000Sub001Block136Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part013] using hcert

def TailChunk000Sub001Block136Part014SupportExplicit : Finset ℕ :=
  ([13898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part014 : ℚ :=
  (754509390625 : ℚ) / 1456820709810545952

def SurrogateDiagonalTailChunk000Sub001Block136Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13898
    = surrogateDiagTailX0RatChunk000Sub001Block136Part014

theorem surrogateDiagonalTailChunk000Sub001Block136Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part014] using hcert

def TailChunk000Sub001Block136Part015SupportExplicit : Finset ℕ :=
  ([13899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part015 : ℚ :=
  (50911515089 : ℚ) / 128928486512394240

def SurrogateDiagonalTailChunk000Sub001Block136Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13899
    = surrogateDiagTailX0RatChunk000Sub001Block136Part015

theorem surrogateDiagonalTailChunk000Sub001Block136Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part015] using hcert

def TailChunk000Sub001Block136Part016SupportExplicit : Finset ℕ :=
  ([13901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part016 : ℚ :=
  (193237801 : ℚ) / 1493502804832800

def SurrogateDiagonalTailChunk000Sub001Block136Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13901
    = surrogateDiagTailX0RatChunk000Sub001Block136Part016

theorem surrogateDiagonalTailChunk000Sub001Block136Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part016] using hcert

def TailChunk000Sub001Block136Part017SupportExplicit : Finset ℕ :=
  ([13902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part017 : ℚ :=
  (27984600197 : ℚ) / 12298088053785600

def SurrogateDiagonalTailChunk000Sub001Block136Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13902
    = surrogateDiagTailX0RatChunk000Sub001Block136Part017

theorem surrogateDiagonalTailChunk000Sub001Block136Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part017] using hcert

def TailChunk000Sub001Block136Part018SupportExplicit : Finset ℕ :=
  ([13903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part018 : ℚ :=
  (3020209515625 : ℚ) / 23349415005139195602

def SurrogateDiagonalTailChunk000Sub001Block136Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13903
    = surrogateDiagTailX0RatChunk000Sub001Block136Part018

theorem surrogateDiagonalTailChunk000Sub001Block136Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part018] using hcert

def TailChunk000Sub001Block136Part019SupportExplicit : Finset ℕ :=
  ([13906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part019 : ℚ :=
  (695838410275 : ℚ) / 1135239387081080832

def SurrogateDiagonalTailChunk000Sub001Block136Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13906
    = surrogateDiagTailX0RatChunk000Sub001Block136Part019

theorem surrogateDiagonalTailChunk000Sub001Block136Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part019] using hcert

def TailChunk000Sub001Block136Part020SupportExplicit : Finset ℕ :=
  ([13907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part020 : ℚ :=
  (3021947640625 : ℚ) / 23376299763444481362

def SurrogateDiagonalTailChunk000Sub001Block136Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13907
    = surrogateDiagTailX0RatChunk000Sub001Block136Part020

theorem surrogateDiagonalTailChunk000Sub001Block136Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part020] using hcert

def TailChunk000Sub001Block136Part021SupportExplicit : Finset ℕ :=
  ([13909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part021 : ℚ :=
  (73206415625 : ℚ) / 393857271015467481

def SurrogateDiagonalTailChunk000Sub001Block136Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13909
    = surrogateDiagTailX0RatChunk000Sub001Block136Part021

theorem surrogateDiagonalTailChunk000Sub001Block136Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part021] using hcert

def TailChunk000Sub001Block136Part022SupportExplicit : Finset ℕ :=
  ([13910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part022 : ℚ :=
  (1025517041375 : ℚ) / 837886655584272384

def SurrogateDiagonalTailChunk000Sub001Block136Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13910
    = surrogateDiagTailX0RatChunk000Sub001Block136Part022

theorem surrogateDiagonalTailChunk000Sub001Block136Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part022] using hcert

def TailChunk000Sub001Block136Part023SupportExplicit : Finset ℕ :=
  ([13911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part023 : ℚ :=
  (5373748536325 : ℚ) / 18480790791475120128

def SurrogateDiagonalTailChunk000Sub001Block136Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13911
    = surrogateDiagTailX0RatChunk000Sub001Block136Part023

theorem surrogateDiagonalTailChunk000Sub001Block136Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part023] using hcert

def TailChunk000Sub001Block136Part024SupportExplicit : Finset ℕ :=
  ([13913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block136Part024 : ℚ :=
  (3024555765625 : ℚ) / 23416670423566152192

def SurrogateDiagonalTailChunk000Sub001Block136Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13913
    = surrogateDiagTailX0RatChunk000Sub001Block136Part024

theorem surrogateDiagonalTailChunk000Sub001Block136Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block136Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block136Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block136Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block136Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block136Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block136Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block136HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block136Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block136Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block136Part000
    + surrogateDiagTailX0RatChunk000Sub001Block136Part001
    + surrogateDiagTailX0RatChunk000Sub001Block136Part002
    + surrogateDiagTailX0RatChunk000Sub001Block136Part003
    + surrogateDiagTailX0RatChunk000Sub001Block136Part004
    + surrogateDiagTailX0RatChunk000Sub001Block136Part005
    + surrogateDiagTailX0RatChunk000Sub001Block136Part006
    + surrogateDiagTailX0RatChunk000Sub001Block136Part007
    + surrogateDiagTailX0RatChunk000Sub001Block136Part008
    + surrogateDiagTailX0RatChunk000Sub001Block136Part009

def surrogateDiagonalTailChunk000Sub001Block136MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block136Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block136Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block136Part010
    + surrogateDiagTailX0RatChunk000Sub001Block136Part011
    + surrogateDiagTailX0RatChunk000Sub001Block136Part012
    + surrogateDiagTailX0RatChunk000Sub001Block136Part013
    + surrogateDiagTailX0RatChunk000Sub001Block136Part014
    + surrogateDiagTailX0RatChunk000Sub001Block136Part015
    + surrogateDiagTailX0RatChunk000Sub001Block136Part016
    + surrogateDiagTailX0RatChunk000Sub001Block136Part017
    + surrogateDiagTailX0RatChunk000Sub001Block136Part018
    + surrogateDiagTailX0RatChunk000Sub001Block136Part019

def surrogateDiagonalTailChunk000Sub001Block136TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block136Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block136Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block136Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block136Part020
    + surrogateDiagTailX0RatChunk000Sub001Block136Part021
    + surrogateDiagTailX0RatChunk000Sub001Block136Part022
    + surrogateDiagTailX0RatChunk000Sub001Block136Part023
    + surrogateDiagTailX0RatChunk000Sub001Block136Part024

def surrogateDiagonalTailChunk000Sub001Block136Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block136HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block136MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block136TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block136 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block136Part000
    + surrogateDiagTailX0RatChunk000Sub001Block136Part001
    + surrogateDiagTailX0RatChunk000Sub001Block136Part002
    + surrogateDiagTailX0RatChunk000Sub001Block136Part003
    + surrogateDiagTailX0RatChunk000Sub001Block136Part004
    + surrogateDiagTailX0RatChunk000Sub001Block136Part005
    + surrogateDiagTailX0RatChunk000Sub001Block136Part006
    + surrogateDiagTailX0RatChunk000Sub001Block136Part007
    + surrogateDiagTailX0RatChunk000Sub001Block136Part008
    + surrogateDiagTailX0RatChunk000Sub001Block136Part009
    + surrogateDiagTailX0RatChunk000Sub001Block136Part010
    + surrogateDiagTailX0RatChunk000Sub001Block136Part011
    + surrogateDiagTailX0RatChunk000Sub001Block136Part012
    + surrogateDiagTailX0RatChunk000Sub001Block136Part013
    + surrogateDiagTailX0RatChunk000Sub001Block136Part014
    + surrogateDiagTailX0RatChunk000Sub001Block136Part015
    + surrogateDiagTailX0RatChunk000Sub001Block136Part016
    + surrogateDiagTailX0RatChunk000Sub001Block136Part017
    + surrogateDiagTailX0RatChunk000Sub001Block136Part018
    + surrogateDiagTailX0RatChunk000Sub001Block136Part019
    + surrogateDiagTailX0RatChunk000Sub001Block136Part020
    + surrogateDiagTailX0RatChunk000Sub001Block136Part021
    + surrogateDiagTailX0RatChunk000Sub001Block136Part022
    + surrogateDiagTailX0RatChunk000Sub001Block136Part023
    + surrogateDiagTailX0RatChunk000Sub001Block136Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block136_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block136Head + surrogateDiagTailX0RatChunk000Sub001Block136Mid + surrogateDiagTailX0RatChunk000Sub001Block136Tail =
      surrogateDiagTailX0RatChunk000Sub001Block136 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block136Head surrogateDiagTailX0RatChunk000Sub001Block136Mid surrogateDiagTailX0RatChunk000Sub001Block136Tail surrogateDiagTailX0RatChunk000Sub001Block136
  ring

def SurrogateDiagonalTailChunk000Sub001Block136HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block136HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block136Head

def SurrogateDiagonalTailChunk000Sub001Block136MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block136MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block136Mid

def SurrogateDiagonalTailChunk000Sub001Block136TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block136TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block136Tail

theorem surrogateDiagonalTailChunk000Sub001Block136_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block136HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block136MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block136TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block136Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block136 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block136HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block136MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block136TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block136Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block136_eq_head_add_mid_add_tail

/-- Block 137 covers tail-support indices [8425,8450) and q from 13917 to 13954. -/

def TailChunk000Sub001Block137Part000SupportExplicit : Finset ℕ :=
  ([13917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part000 : ℚ :=
  (5378385536125 : ℚ) / 18512702358909199488

def SurrogateDiagonalTailChunk000Sub001Block137Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13917
    = surrogateDiagTailX0RatChunk000Sub001Block137Part000

theorem surrogateDiagonalTailChunk000Sub001Block137Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part000] using hcert

def TailChunk000Sub001Block137Part001SupportExplicit : Finset ℕ :=
  ([13918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part001 : ℚ :=
  (756682515625 : ℚ) / 1465225826972890962

def SurrogateDiagonalTailChunk000Sub001Block137Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13918
    = surrogateDiagTailX0RatChunk000Sub001Block137Part001

theorem surrogateDiagonalTailChunk000Sub001Block137Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part001] using hcert

def TailChunk000Sub001Block137Part002SupportExplicit : Finset ℕ :=
  ([13919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part002 : ℚ :=
  (91404931937 : ℚ) / 652700462968995840

def SurrogateDiagonalTailChunk000Sub001Block137Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13919
    = surrogateDiagTailX0RatChunk000Sub001Block137Part002

theorem surrogateDiagonalTailChunk000Sub001Block137Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part002] using hcert

def TailChunk000Sub001Block137Part003SupportExplicit : Finset ℕ :=
  ([13921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part003 : ℚ :=
  (4844856025 : ℚ) / 37552926852513792

def SurrogateDiagonalTailChunk000Sub001Block137Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13921
    = surrogateDiagTailX0RatChunk000Sub001Block137Part003

theorem surrogateDiagonalTailChunk000Sub001Block137Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part003] using hcert

def TailChunk000Sub001Block137Part004SupportExplicit : Finset ℕ :=
  ([13922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part004 : ℚ :=
  (1211388025 : ℚ) / 2347057928282112

def SurrogateDiagonalTailChunk000Sub001Block137Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13922
    = surrogateDiagTailX0RatChunk000Sub001Block137Part004

theorem surrogateDiagonalTailChunk000Sub001Block137Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part004] using hcert

def TailChunk000Sub001Block137Part005SupportExplicit : Finset ℕ :=
  ([13926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part005 : ℚ :=
  (1670117359 : ℚ) / 864532872000000

def SurrogateDiagonalTailChunk000Sub001Block137Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13926
    = surrogateDiagTailX0RatChunk000Sub001Block137Part005

theorem surrogateDiagonalTailChunk000Sub001Block137Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part005] using hcert

def TailChunk000Sub001Block137Part006SupportExplicit : Finset ℕ :=
  ([13927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part006 : ℚ :=
  (5512275516425 : ℚ) / 37681762490359686144

def SurrogateDiagonalTailChunk000Sub001Block137Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13927
    = surrogateDiagTailX0RatChunk000Sub001Block137Part006

theorem surrogateDiagonalTailChunk000Sub001Block137Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part006] using hcert

def TailChunk000Sub001Block137Part007SupportExplicit : Finset ℕ :=
  ([13929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part007 : ℚ :=
  (489787775975 : ℚ) / 1688786314346364288

def SurrogateDiagonalTailChunk000Sub001Block137Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13929
    = surrogateDiagTailX0RatChunk000Sub001Block137Part007

theorem surrogateDiagonalTailChunk000Sub001Block137Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part007] using hcert

def TailChunk000Sub001Block137Part008SupportExplicit : Finset ℕ :=
  ([13930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part008 : ℚ :=
  (941125364225 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub001Block137Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13930
    = surrogateDiagTailX0RatChunk000Sub001Block137Part008

theorem surrogateDiagonalTailChunk000Sub001Block137Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part008] using hcert

def TailChunk000Sub001Block137Part009SupportExplicit : Finset ℕ :=
  ([13931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part009 : ℚ :=
  (4851819025 : ℚ) / 37660953900653202

def SurrogateDiagonalTailChunk000Sub001Block137Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13931
    = surrogateDiagTailX0RatChunk000Sub001Block137Part009

theorem surrogateDiagonalTailChunk000Sub001Block137Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part009] using hcert

def TailChunk000Sub001Block137Part010SupportExplicit : Finset ℕ :=
  ([13933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part010 : ℚ :=
  (3033257640625 : ℚ) / 23551617029773008672

def SurrogateDiagonalTailChunk000Sub001Block137Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13933
    = surrogateDiagTailX0RatChunk000Sub001Block137Part010

theorem surrogateDiagonalTailChunk000Sub001Block137Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part010] using hcert

def TailChunk000Sub001Block137Part011SupportExplicit : Finset ℕ :=
  ([13934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part011 : ℚ :=
  (758423265625 : ℚ) / 1471976064360813042

def SurrogateDiagonalTailChunk000Sub001Block137Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13934
    = surrogateDiagTailX0RatChunk000Sub001Block137Part011

theorem surrogateDiagonalTailChunk000Sub001Block137Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part011] using hcert

def TailChunk000Sub001Block137Part012SupportExplicit : Finset ℕ :=
  ([13935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part012 : ℚ :=
  (3823888566925 : ℚ) / 7595890784587481088

def SurrogateDiagonalTailChunk000Sub001Block137Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13935
    = surrogateDiagTailX0RatChunk000Sub001Block137Part012

theorem surrogateDiagonalTailChunk000Sub001Block137Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part012] using hcert

def TailChunk000Sub001Block137Part013SupportExplicit : Finset ℕ :=
  ([13937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part013 : ℚ :=
  (311064764263 : ℚ) / 1360761057792000000

def SurrogateDiagonalTailChunk000Sub001Block137Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13937
    = surrogateDiagTailX0RatChunk000Sub001Block137Part013

theorem surrogateDiagonalTailChunk000Sub001Block137Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part013] using hcert

def TailChunk000Sub001Block137Part014SupportExplicit : Finset ℕ :=
  ([13938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part014 : ℚ :=
  (31687998581 : ℚ) / 18744228096000000

def SurrogateDiagonalTailChunk000Sub001Block137Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13938
    = surrogateDiagTailX0RatChunk000Sub001Block137Part014

theorem surrogateDiagonalTailChunk000Sub001Block137Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part014] using hcert

def TailChunk000Sub001Block137Part015SupportExplicit : Finset ℕ :=
  ([13939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part015 : ℚ :=
  (1461949868075 : ℚ) / 10768504942246062336

def SurrogateDiagonalTailChunk000Sub001Block137Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13939
    = surrogateDiagTailX0RatChunk000Sub001Block137Part015

theorem surrogateDiagonalTailChunk000Sub001Block137Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part015] using hcert

def TailChunk000Sub001Block137Part016SupportExplicit : Finset ℕ :=
  ([13942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part016 : ℚ :=
  (1214871025 : ℚ) / 2360575865578962

def SurrogateDiagonalTailChunk000Sub001Block137Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13942
    = surrogateDiagTailX0RatChunk000Sub001Block137Part016

theorem surrogateDiagonalTailChunk000Sub001Block137Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part016] using hcert

def TailChunk000Sub001Block137Part017SupportExplicit : Finset ℕ :=
  ([13943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part017 : ℚ :=
  (47104641247 : ℚ) / 350292823333355520

def SurrogateDiagonalTailChunk000Sub001Block137Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13943
    = surrogateDiagTailX0RatChunk000Sub001Block137Part017

theorem surrogateDiagonalTailChunk000Sub001Block137Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part017] using hcert

def TailChunk000Sub001Block137Part018SupportExplicit : Finset ℕ :=
  ([13945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part018 : ℚ :=
  (8260780690975 : ℚ) / 38675674981645713408

def SurrogateDiagonalTailChunk000Sub001Block137Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13945
    = surrogateDiagTailX0RatChunk000Sub001Block137Part018

theorem surrogateDiagonalTailChunk000Sub001Block137Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part018] using hcert

def TailChunk000Sub001Block137Part019SupportExplicit : Finset ℕ :=
  ([13946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part019 : ℚ :=
  (78543672175 : ℚ) / 130839453091526688

def SurrogateDiagonalTailChunk000Sub001Block137Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13946
    = surrogateDiagTailX0RatChunk000Sub001Block137Part019

theorem surrogateDiagonalTailChunk000Sub001Block137Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part019] using hcert

def TailChunk000Sub001Block137Part020SupportExplicit : Finset ℕ :=
  ([13947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part020 : ℚ :=
  (5401600535125 : ℚ) / 18672880550992969728

def SurrogateDiagonalTailChunk000Sub001Block137Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13947
    = surrogateDiagTailX0RatChunk000Sub001Block137Part020

theorem surrogateDiagonalTailChunk000Sub001Block137Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part020] using hcert

def TailChunk000Sub001Block137Part021SupportExplicit : Finset ℕ :=
  ([13949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part021 : ℚ :=
  (1201264323725 : ℚ) / 6691199589905596416

def SurrogateDiagonalTailChunk000Sub001Block137Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13949
    = surrogateDiagTailX0RatChunk000Sub001Block137Part021

theorem surrogateDiagonalTailChunk000Sub001Block137Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part021] using hcert

def TailChunk000Sub001Block137Part022SupportExplicit : Finset ℕ :=
  ([13951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part022 : ℚ :=
  (2356778564875 : ℚ) / 12756431621726871552

def SurrogateDiagonalTailChunk000Sub001Block137Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13951
    = surrogateDiagTailX0RatChunk000Sub001Block137Part022

theorem surrogateDiagonalTailChunk000Sub001Block137Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part022] using hcert

def TailChunk000Sub001Block137Part023SupportExplicit : Finset ℕ :=
  ([13953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part023 : ℚ :=
  (216249981397 : ℚ) / 748201620402000000

def SurrogateDiagonalTailChunk000Sub001Block137Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13953
    = surrogateDiagTailX0RatChunk000Sub001Block137Part023

theorem surrogateDiagonalTailChunk000Sub001Block137Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part023] using hcert

def TailChunk000Sub001Block137Part024SupportExplicit : Finset ℕ :=
  ([13954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block137Part024 : ℚ :=
  (760602015625 : ℚ) / 1480446628407017472

def SurrogateDiagonalTailChunk000Sub001Block137Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13954
    = surrogateDiagTailX0RatChunk000Sub001Block137Part024

theorem surrogateDiagonalTailChunk000Sub001Block137Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block137Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block137Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block137Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block137Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block137Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block137Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block137HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block137Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block137Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block137Part000
    + surrogateDiagTailX0RatChunk000Sub001Block137Part001
    + surrogateDiagTailX0RatChunk000Sub001Block137Part002
    + surrogateDiagTailX0RatChunk000Sub001Block137Part003
    + surrogateDiagTailX0RatChunk000Sub001Block137Part004
    + surrogateDiagTailX0RatChunk000Sub001Block137Part005
    + surrogateDiagTailX0RatChunk000Sub001Block137Part006
    + surrogateDiagTailX0RatChunk000Sub001Block137Part007
    + surrogateDiagTailX0RatChunk000Sub001Block137Part008
    + surrogateDiagTailX0RatChunk000Sub001Block137Part009

def surrogateDiagonalTailChunk000Sub001Block137MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block137Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block137Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block137Part010
    + surrogateDiagTailX0RatChunk000Sub001Block137Part011
    + surrogateDiagTailX0RatChunk000Sub001Block137Part012
    + surrogateDiagTailX0RatChunk000Sub001Block137Part013
    + surrogateDiagTailX0RatChunk000Sub001Block137Part014
    + surrogateDiagTailX0RatChunk000Sub001Block137Part015
    + surrogateDiagTailX0RatChunk000Sub001Block137Part016
    + surrogateDiagTailX0RatChunk000Sub001Block137Part017
    + surrogateDiagTailX0RatChunk000Sub001Block137Part018
    + surrogateDiagTailX0RatChunk000Sub001Block137Part019

def surrogateDiagonalTailChunk000Sub001Block137TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block137Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block137Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block137Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block137Part020
    + surrogateDiagTailX0RatChunk000Sub001Block137Part021
    + surrogateDiagTailX0RatChunk000Sub001Block137Part022
    + surrogateDiagTailX0RatChunk000Sub001Block137Part023
    + surrogateDiagTailX0RatChunk000Sub001Block137Part024

def surrogateDiagonalTailChunk000Sub001Block137Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block137HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block137MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block137TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block137 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block137Part000
    + surrogateDiagTailX0RatChunk000Sub001Block137Part001
    + surrogateDiagTailX0RatChunk000Sub001Block137Part002
    + surrogateDiagTailX0RatChunk000Sub001Block137Part003
    + surrogateDiagTailX0RatChunk000Sub001Block137Part004
    + surrogateDiagTailX0RatChunk000Sub001Block137Part005
    + surrogateDiagTailX0RatChunk000Sub001Block137Part006
    + surrogateDiagTailX0RatChunk000Sub001Block137Part007
    + surrogateDiagTailX0RatChunk000Sub001Block137Part008
    + surrogateDiagTailX0RatChunk000Sub001Block137Part009
    + surrogateDiagTailX0RatChunk000Sub001Block137Part010
    + surrogateDiagTailX0RatChunk000Sub001Block137Part011
    + surrogateDiagTailX0RatChunk000Sub001Block137Part012
    + surrogateDiagTailX0RatChunk000Sub001Block137Part013
    + surrogateDiagTailX0RatChunk000Sub001Block137Part014
    + surrogateDiagTailX0RatChunk000Sub001Block137Part015
    + surrogateDiagTailX0RatChunk000Sub001Block137Part016
    + surrogateDiagTailX0RatChunk000Sub001Block137Part017
    + surrogateDiagTailX0RatChunk000Sub001Block137Part018
    + surrogateDiagTailX0RatChunk000Sub001Block137Part019
    + surrogateDiagTailX0RatChunk000Sub001Block137Part020
    + surrogateDiagTailX0RatChunk000Sub001Block137Part021
    + surrogateDiagTailX0RatChunk000Sub001Block137Part022
    + surrogateDiagTailX0RatChunk000Sub001Block137Part023
    + surrogateDiagTailX0RatChunk000Sub001Block137Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block137_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block137Head + surrogateDiagTailX0RatChunk000Sub001Block137Mid + surrogateDiagTailX0RatChunk000Sub001Block137Tail =
      surrogateDiagTailX0RatChunk000Sub001Block137 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block137Head surrogateDiagTailX0RatChunk000Sub001Block137Mid surrogateDiagTailX0RatChunk000Sub001Block137Tail surrogateDiagTailX0RatChunk000Sub001Block137
  ring

def SurrogateDiagonalTailChunk000Sub001Block137HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block137HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block137Head

def SurrogateDiagonalTailChunk000Sub001Block137MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block137MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block137Mid

def SurrogateDiagonalTailChunk000Sub001Block137TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block137TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block137Tail

theorem surrogateDiagonalTailChunk000Sub001Block137_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block137HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block137MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block137TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block137Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block137 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block137HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block137MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block137TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block137Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block137_eq_head_add_mid_add_tail

/-- Block 138 covers tail-support indices [8450,8475) and q from 13955 to 13994. -/

def TailChunk000Sub001Block138Part000SupportExplicit : Finset ℕ :=
  ([13955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part000 : ℚ :=
  (259511675 : ℚ) / 1292892400054656

def SurrogateDiagonalTailChunk000Sub001Block138Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13955
    = surrogateDiagTailX0RatChunk000Sub001Block138Part000

theorem surrogateDiagonalTailChunk000Sub001Block138Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part000] using hcert

def TailChunk000Sub001Block138Part001SupportExplicit : Finset ℕ :=
  ([13957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part001 : ℚ :=
  (438987256477 : ℚ) / 2963617771369267200

def SurrogateDiagonalTailChunk000Sub001Block138Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13957
    = surrogateDiagTailX0RatChunk000Sub001Block138Part001

theorem surrogateDiagonalTailChunk000Sub001Block138Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part001] using hcert

def TailChunk000Sub001Block138Part002SupportExplicit : Finset ℕ :=
  ([13958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part002 : ℚ :=
  (2482358469775 : ℚ) / 3189107905431717888

def SurrogateDiagonalTailChunk000Sub001Block138Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13958
    = surrogateDiagTailX0RatChunk000Sub001Block138Part002

theorem surrogateDiagonalTailChunk000Sub001Block138Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part002] using hcert

def TailChunk000Sub001Block138Part003SupportExplicit : Finset ℕ :=
  ([13961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part003 : ℚ :=
  (5638802024825 : ℚ) / 39498270815130836544

def SurrogateDiagonalTailChunk000Sub001Block138Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13961
    = surrogateDiagTailX0RatChunk000Sub001Block138Part003

theorem surrogateDiagonalTailChunk000Sub001Block138Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part003] using hcert

def TailChunk000Sub001Block138Part004SupportExplicit : Finset ℕ :=
  ([13962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part004 : ℚ :=
  (302628645175 : ℚ) / 138803553493106688

def SurrogateDiagonalTailChunk000Sub001Block138Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13962
    = surrogateDiagTailX0RatChunk000Sub001Block138Part004

theorem surrogateDiagonalTailChunk000Sub001Block138Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part004] using hcert

def TailChunk000Sub001Block138Part005SupportExplicit : Finset ℕ :=
  ([13963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part005 : ℚ :=
  (3046333890625 : ℚ) / 23755129496667366642

def SurrogateDiagonalTailChunk000Sub001Block138Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13963
    = surrogateDiagTailX0RatChunk000Sub001Block138Part005

theorem surrogateDiagonalTailChunk000Sub001Block138Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part005] using hcert

def TailChunk000Sub001Block138Part006SupportExplicit : Finset ℕ :=
  ([13966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part006 : ℚ :=
  (761910765625 : ℚ) / 1485546482892211122

def SurrogateDiagonalTailChunk000Sub001Block138Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13966
    = surrogateDiagTailX0RatChunk000Sub001Block138Part006

theorem surrogateDiagonalTailChunk000Sub001Block138Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part006] using hcert

def TailChunk000Sub001Block138Part007SupportExplicit : Finset ℕ :=
  ([13967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part007 : ℚ :=
  (3048079515625 : ℚ) / 23782363806852249042

def SurrogateDiagonalTailChunk000Sub001Block138Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13967
    = surrogateDiagTailX0RatChunk000Sub001Block138Part007

theorem surrogateDiagonalTailChunk000Sub001Block138Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part007] using hcert

def TailChunk000Sub001Block138Part008SupportExplicit : Finset ℕ :=
  ([13969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part008 : ℚ :=
  (471380797831 : ℚ) / 3502928233333555200

def SurrogateDiagonalTailChunk000Sub001Block138Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13969
    = surrogateDiagTailX0RatChunk000Sub001Block138Part008

theorem surrogateDiagonalTailChunk000Sub001Block138Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part008] using hcert

def TailChunk000Sub001Block138Part009SupportExplicit : Finset ℕ :=
  ([13970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part009 : ℚ :=
  (83141297 : ℚ) / 65854115389440

def SurrogateDiagonalTailChunk000Sub001Block138Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13970
    = surrogateDiagTailX0RatChunk000Sub001Block138Part009

theorem surrogateDiagonalTailChunk000Sub001Block138Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part009] using hcert

def TailChunk000Sub001Block138Part010SupportExplicit : Finset ℕ :=
  ([13971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part010 : ℚ :=
  (5420208534325 : ℚ) / 18801769671169671168

def SurrogateDiagonalTailChunk000Sub001Block138Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13971
    = surrogateDiagTailX0RatChunk000Sub001Block138Part010

theorem surrogateDiagonalTailChunk000Sub001Block138Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part010] using hcert

def TailChunk000Sub001Block138Part011SupportExplicit : Finset ℕ :=
  ([13973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part011 : ℚ :=
  (123485121725 : ℚ) / 925091536866951168

def SurrogateDiagonalTailChunk000Sub001Block138Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13973
    = surrogateDiagTailX0RatChunk000Sub001Block138Part011

theorem surrogateDiagonalTailChunk000Sub001Block138Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part011] using hcert

def TailChunk000Sub001Block138Part012SupportExplicit : Finset ℕ :=
  ([13974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part012 : ℚ :=
  (522812583525 : ℚ) / 298993089601601536

def SurrogateDiagonalTailChunk000Sub001Block138Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13974
    = surrogateDiagTailX0RatChunk000Sub001Block138Part012

theorem surrogateDiagonalTailChunk000Sub001Block138Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part012] using hcert

def TailChunk000Sub001Block138Part013SupportExplicit : Finset ℕ :=
  ([13978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part013 : ℚ :=
  (3226236761 : ℚ) / 5665802629939200

def SurrogateDiagonalTailChunk000Sub001Block138Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13978
    = surrogateDiagTailX0RatChunk000Sub001Block138Part013

theorem surrogateDiagonalTailChunk000Sub001Block138Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part013] using hcert

def TailChunk000Sub001Block138Part014SupportExplicit : Finset ℕ :=
  ([13979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part014 : ℚ :=
  (9215505105025 : ℚ) / 51436807806449829888

def SurrogateDiagonalTailChunk000Sub001Block138Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13979
    = surrogateDiagTailX0RatChunk000Sub001Block138Part014

theorem surrogateDiagonalTailChunk000Sub001Block138Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part014] using hcert

def TailChunk000Sub001Block138Part015SupportExplicit : Finset ℕ :=
  ([13981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part015 : ℚ :=
  (25242216917 : ℚ) / 138267648000000000

def SurrogateDiagonalTailChunk000Sub001Block138Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13981
    = surrogateDiagTailX0RatChunk000Sub001Block138Part015

theorem surrogateDiagonalTailChunk000Sub001Block138Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part015] using hcert

def TailChunk000Sub001Block138Part016SupportExplicit : Finset ℕ :=
  ([13982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part016 : ℚ :=
  (1221852025 : ℚ) / 2387786833884402

def SurrogateDiagonalTailChunk000Sub001Block138Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13982
    = surrogateDiagTailX0RatChunk000Sub001Block138Part016

theorem surrogateDiagonalTailChunk000Sub001Block138Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part016] using hcert

def TailChunk000Sub001Block138Part017SupportExplicit : Finset ℕ :=
  ([13983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part017 : ℚ :=
  (22217709925 : ℚ) / 71617864839386112

def SurrogateDiagonalTailChunk000Sub001Block138Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13983
    = surrogateDiagTailX0RatChunk000Sub001Block138Part017

theorem surrogateDiagonalTailChunk000Sub001Block138Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part017] using hcert

def TailChunk000Sub001Block138Part018SupportExplicit : Finset ℕ :=
  ([13985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part018 : ℚ :=
  (8308249158775 : ℚ) / 39121499486362042368

def SurrogateDiagonalTailChunk000Sub001Block138Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13985
    = surrogateDiagTailX0RatChunk000Sub001Block138Part018

theorem surrogateDiagonalTailChunk000Sub001Block138Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part018] using hcert

def TailChunk000Sub001Block138Part019SupportExplicit : Finset ℕ :=
  ([13987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part019 : ℚ :=
  (22562470851 : ℚ) / 168765628445747200

def SurrogateDiagonalTailChunk000Sub001Block138Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13987
    = surrogateDiagTailX0RatChunk000Sub001Block138Part019

theorem surrogateDiagonalTailChunk000Sub001Block138Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part019] using hcert

def TailChunk000Sub001Block138Part020SupportExplicit : Finset ℕ :=
  ([13989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part020 : ℚ :=
  (5434185533725 : ℚ) / 18898873508959452288

def SurrogateDiagonalTailChunk000Sub001Block138Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13989
    = surrogateDiagTailX0RatChunk000Sub001Block138Part020

theorem surrogateDiagonalTailChunk000Sub001Block138Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part020] using hcert

def TailChunk000Sub001Block138Part021SupportExplicit : Finset ℕ :=
  ([13990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part021 : ℚ :=
  (2200296785425 : ℚ) / 2445093717897627648

def SurrogateDiagonalTailChunk000Sub001Block138Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13990
    = surrogateDiagTailX0RatChunk000Sub001Block138Part021

theorem surrogateDiagonalTailChunk000Sub001Block138Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part021] using hcert

def TailChunk000Sub001Block138Part022SupportExplicit : Finset ℕ :=
  ([13991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part022 : ℚ :=
  (11028257401225 : ℚ) / 74815926702828945408

def SurrogateDiagonalTailChunk000Sub001Block138Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13991
    = surrogateDiagTailX0RatChunk000Sub001Block138Part022

theorem surrogateDiagonalTailChunk000Sub001Block138Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part022] using hcert

def TailChunk000Sub001Block138Part023SupportExplicit : Finset ℕ :=
  ([13993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part023 : ℚ :=
  (9233978551225 : ℚ) / 51643277422858378368

def SurrogateDiagonalTailChunk000Sub001Block138Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13993
    = surrogateDiagTailX0RatChunk000Sub001Block138Part023

theorem surrogateDiagonalTailChunk000Sub001Block138Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part023] using hcert

def TailChunk000Sub001Block138Part024SupportExplicit : Finset ℕ :=
  ([13994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block138Part024 : ℚ :=
  (764968890625 : ℚ) / 1497497378467936032

def SurrogateDiagonalTailChunk000Sub001Block138Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13994
    = surrogateDiagTailX0RatChunk000Sub001Block138Part024

theorem surrogateDiagonalTailChunk000Sub001Block138Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block138Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block138Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block138Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block138Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block138Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block138Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block138HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block138Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block138Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block138Part000
    + surrogateDiagTailX0RatChunk000Sub001Block138Part001
    + surrogateDiagTailX0RatChunk000Sub001Block138Part002
    + surrogateDiagTailX0RatChunk000Sub001Block138Part003
    + surrogateDiagTailX0RatChunk000Sub001Block138Part004
    + surrogateDiagTailX0RatChunk000Sub001Block138Part005
    + surrogateDiagTailX0RatChunk000Sub001Block138Part006
    + surrogateDiagTailX0RatChunk000Sub001Block138Part007
    + surrogateDiagTailX0RatChunk000Sub001Block138Part008
    + surrogateDiagTailX0RatChunk000Sub001Block138Part009

def surrogateDiagonalTailChunk000Sub001Block138MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block138Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block138Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block138Part010
    + surrogateDiagTailX0RatChunk000Sub001Block138Part011
    + surrogateDiagTailX0RatChunk000Sub001Block138Part012
    + surrogateDiagTailX0RatChunk000Sub001Block138Part013
    + surrogateDiagTailX0RatChunk000Sub001Block138Part014
    + surrogateDiagTailX0RatChunk000Sub001Block138Part015
    + surrogateDiagTailX0RatChunk000Sub001Block138Part016
    + surrogateDiagTailX0RatChunk000Sub001Block138Part017
    + surrogateDiagTailX0RatChunk000Sub001Block138Part018
    + surrogateDiagTailX0RatChunk000Sub001Block138Part019

def surrogateDiagonalTailChunk000Sub001Block138TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block138Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block138Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block138Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block138Part020
    + surrogateDiagTailX0RatChunk000Sub001Block138Part021
    + surrogateDiagTailX0RatChunk000Sub001Block138Part022
    + surrogateDiagTailX0RatChunk000Sub001Block138Part023
    + surrogateDiagTailX0RatChunk000Sub001Block138Part024

def surrogateDiagonalTailChunk000Sub001Block138Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block138HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block138MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block138TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block138 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block138Part000
    + surrogateDiagTailX0RatChunk000Sub001Block138Part001
    + surrogateDiagTailX0RatChunk000Sub001Block138Part002
    + surrogateDiagTailX0RatChunk000Sub001Block138Part003
    + surrogateDiagTailX0RatChunk000Sub001Block138Part004
    + surrogateDiagTailX0RatChunk000Sub001Block138Part005
    + surrogateDiagTailX0RatChunk000Sub001Block138Part006
    + surrogateDiagTailX0RatChunk000Sub001Block138Part007
    + surrogateDiagTailX0RatChunk000Sub001Block138Part008
    + surrogateDiagTailX0RatChunk000Sub001Block138Part009
    + surrogateDiagTailX0RatChunk000Sub001Block138Part010
    + surrogateDiagTailX0RatChunk000Sub001Block138Part011
    + surrogateDiagTailX0RatChunk000Sub001Block138Part012
    + surrogateDiagTailX0RatChunk000Sub001Block138Part013
    + surrogateDiagTailX0RatChunk000Sub001Block138Part014
    + surrogateDiagTailX0RatChunk000Sub001Block138Part015
    + surrogateDiagTailX0RatChunk000Sub001Block138Part016
    + surrogateDiagTailX0RatChunk000Sub001Block138Part017
    + surrogateDiagTailX0RatChunk000Sub001Block138Part018
    + surrogateDiagTailX0RatChunk000Sub001Block138Part019
    + surrogateDiagTailX0RatChunk000Sub001Block138Part020
    + surrogateDiagTailX0RatChunk000Sub001Block138Part021
    + surrogateDiagTailX0RatChunk000Sub001Block138Part022
    + surrogateDiagTailX0RatChunk000Sub001Block138Part023
    + surrogateDiagTailX0RatChunk000Sub001Block138Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block138_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block138Head + surrogateDiagTailX0RatChunk000Sub001Block138Mid + surrogateDiagTailX0RatChunk000Sub001Block138Tail =
      surrogateDiagTailX0RatChunk000Sub001Block138 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block138Head surrogateDiagTailX0RatChunk000Sub001Block138Mid surrogateDiagTailX0RatChunk000Sub001Block138Tail surrogateDiagTailX0RatChunk000Sub001Block138
  ring

def SurrogateDiagonalTailChunk000Sub001Block138HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block138HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block138Head

def SurrogateDiagonalTailChunk000Sub001Block138MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block138MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block138Mid

def SurrogateDiagonalTailChunk000Sub001Block138TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block138TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block138Tail

theorem surrogateDiagonalTailChunk000Sub001Block138_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block138HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block138MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block138TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block138Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block138 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block138HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block138MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block138TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block138Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block138_eq_head_add_mid_add_tail

/-- Block 139 covers tail-support indices [8475,8500) and q from 13997 to 14037. -/

def TailChunk000Sub001Block139Part000SupportExplicit : Finset ℕ :=
  ([13997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part000 : ℚ :=
  (3061187640625 : ℚ) / 23987368272111712032

def SurrogateDiagonalTailChunk000Sub001Block139Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13997
    = surrogateDiagTailX0RatChunk000Sub001Block139Part000

theorem surrogateDiagonalTailChunk000Sub001Block139Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part000] using hcert

def TailChunk000Sub001Block139Part001SupportExplicit : Finset ℕ :=
  ([13998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part001 : ℚ :=
  (850170895175 : ℚ) / 591603902604616704

def SurrogateDiagonalTailChunk000Sub001Block139Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13998
    = surrogateDiagTailX0RatChunk000Sub001Block139Part001

theorem surrogateDiagonalTailChunk000Sub001Block139Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part001] using hcert

def TailChunk000Sub001Block139Part002SupportExplicit : Finset ℕ :=
  ([13999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part002 : ℚ :=
  (3062062515625 : ℚ) / 24001082196307954002

def SurrogateDiagonalTailChunk000Sub001Block139Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 13999
    = surrogateDiagTailX0RatChunk000Sub001Block139Part002

theorem surrogateDiagonalTailChunk000Sub001Block139Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part002] using hcert

def TailChunk000Sub001Block139Part003SupportExplicit : Finset ℕ :=
  ([14001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part003 : ℚ :=
  (1599094467575 : ℚ) / 4542371785224585216

def SurrogateDiagonalTailChunk000Sub001Block139Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14001
    = surrogateDiagTailX0RatChunk000Sub001Block139Part003

theorem surrogateDiagonalTailChunk000Sub001Block139Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part003] using hcert

def TailChunk000Sub001Block139Part004SupportExplicit : Finset ℕ :=
  ([14002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part004 : ℚ :=
  (49014001 : ℚ) / 96059208000000

def SurrogateDiagonalTailChunk000Sub001Block139Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14002
    = surrogateDiagTailX0RatChunk000Sub001Block139Part004

theorem surrogateDiagonalTailChunk000Sub001Block139Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part004] using hcert

def TailChunk000Sub001Block139Part005SupportExplicit : Finset ℕ :=
  ([14003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part005 : ℚ :=
  (372870125467 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk000Sub001Block139Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14003
    = surrogateDiagTailX0RatChunk000Sub001Block139Part005

theorem surrogateDiagonalTailChunk000Sub001Block139Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part005] using hcert

def TailChunk000Sub001Block139Part006SupportExplicit : Finset ℕ :=
  ([14005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part006 : ℚ :=
  (333281375899 : ℚ) / 1573834063872000000

def SurrogateDiagonalTailChunk000Sub001Block139Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14005
    = surrogateDiagTailX0RatChunk000Sub001Block139Part006

theorem surrogateDiagonalTailChunk000Sub001Block139Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part006] using hcert

def TailChunk000Sub001Block139Part007SupportExplicit : Finset ℕ :=
  ([14006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part007 : ℚ :=
  (985571511675 : ℚ) / 1790539031274428416

def SurrogateDiagonalTailChunk000Sub001Block139Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14006
    = surrogateDiagTailX0RatChunk000Sub001Block139Part007

theorem surrogateDiagonalTailChunk000Sub001Block139Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part007] using hcert

def TailChunk000Sub001Block139Part008SupportExplicit : Finset ℕ :=
  ([14007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part008 : ℚ :=
  (138966612325 : ℚ) / 266634695265878016

def SurrogateDiagonalTailChunk000Sub001Block139Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14007
    = surrogateDiagTailX0RatChunk000Sub001Block139Part008

theorem surrogateDiagonalTailChunk000Sub001Block139Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part008] using hcert

def TailChunk000Sub001Block139Part009SupportExplicit : Finset ℕ :=
  ([14009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part009 : ℚ :=
  (3066438765625 : ℚ) / 24069740043334144512

def SurrogateDiagonalTailChunk000Sub001Block139Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14009
    = surrogateDiagTailX0RatChunk000Sub001Block139Part009

theorem surrogateDiagonalTailChunk000Sub001Block139Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part009] using hcert

def TailChunk000Sub001Block139Part010SupportExplicit : Finset ℕ :=
  ([14010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part010 : ℚ :=
  (222132821475 : ℚ) / 80496912523378688

def SurrogateDiagonalTailChunk000Sub001Block139Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14010
    = surrogateDiagTailX0RatChunk000Sub001Block139Part010

theorem surrogateDiagonalTailChunk000Sub001Block139Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part010] using hcert

def TailChunk000Sub001Block139Part011SupportExplicit : Finset ℕ :=
  ([14011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part011 : ℚ :=
  (4907703025 : ℚ) / 38533582831541202

def SurrogateDiagonalTailChunk000Sub001Block139Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14011
    = surrogateDiagTailX0RatChunk000Sub001Block139Part011

theorem surrogateDiagonalTailChunk000Sub001Block139Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part011] using hcert

def TailChunk000Sub001Block139Part012SupportExplicit : Finset ℕ :=
  ([14015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part012 : ℚ :=
  (8343939768025 : ℚ) / 39458388819498190848

def SurrogateDiagonalTailChunk000Sub001Block139Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14015
    = surrogateDiagTailX0RatChunk000Sub001Block139Part012

theorem surrogateDiagonalTailChunk000Sub001Block139Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part012] using hcert

def TailChunk000Sub001Block139Part013SupportExplicit : Finset ℕ :=
  ([14017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part013 : ℚ :=
  (59705450147 : ℚ) / 450810199693136400

def SurrogateDiagonalTailChunk000Sub001Block139Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14017
    = surrogateDiagTailX0RatChunk000Sub001Block139Part013

theorem surrogateDiagonalTailChunk000Sub001Block139Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part013] using hcert

def TailChunk000Sub001Block139Part014SupportExplicit : Finset ℕ :=
  ([14018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part014 : ℚ :=
  (46924534075 : ℚ) / 85063555054429056

def SurrogateDiagonalTailChunk000Sub001Block139Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14018
    = surrogateDiagTailX0RatChunk000Sub001Block139Part014

theorem surrogateDiagonalTailChunk000Sub001Block139Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part014] using hcert

def TailChunk000Sub001Block139Part015SupportExplicit : Finset ℕ :=
  ([14019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part015 : ℚ :=
  (3411418099925 : ℚ) / 9530774239234228224

def SurrogateDiagonalTailChunk000Sub001Block139Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14019
    = surrogateDiagTailX0RatChunk000Sub001Block139Part015

theorem surrogateDiagonalTailChunk000Sub001Block139Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part015] using hcert

def TailChunk000Sub001Block139Part016SupportExplicit : Finset ℕ :=
  ([14021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part016 : ℚ :=
  (10627212875 : ℚ) / 58100536586675583

def SurrogateDiagonalTailChunk000Sub001Block139Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14021
    = surrogateDiagTailX0RatChunk000Sub001Block139Part016

theorem surrogateDiagonalTailChunk000Sub001Block139Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part016] using hcert

def TailChunk000Sub001Block139Part017SupportExplicit : Finset ℕ :=
  ([14023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part017 : ℚ :=
  (1299247464425 : ℚ) / 9527118166096054272

def SurrogateDiagonalTailChunk000Sub001Block139Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14023
    = surrogateDiagTailX0RatChunk000Sub001Block139Part017

theorem surrogateDiagonalTailChunk000Sub001Block139Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part017] using hcert

def TailChunk000Sub001Block139Part018SupportExplicit : Finset ℕ :=
  ([14026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part018 : ℚ :=
  (768471390625 : ℚ) / 1511243678551010592

def SurrogateDiagonalTailChunk000Sub001Block139Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14026
    = surrogateDiagTailX0RatChunk000Sub001Block139Part018

theorem surrogateDiagonalTailChunk000Sub001Block139Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part018] using hcert

def TailChunk000Sub001Block139Part019SupportExplicit : Finset ℕ :=
  ([14029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block139Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14029
    = surrogateDiagTailX0RatChunk000Sub001Block139Part019

theorem surrogateDiagonalTailChunk000Sub001Block139Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part019] using hcert

def TailChunk000Sub001Block139Part020SupportExplicit : Finset ℕ :=
  ([14030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part020 : ℚ :=
  (2839729861 : ℚ) / 12956010459955200

def SurrogateDiagonalTailChunk000Sub001Block139Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14030
    = surrogateDiagTailX0RatChunk000Sub001Block139Part020

theorem surrogateDiagonalTailChunk000Sub001Block139Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part020] using hcert

def TailChunk000Sub001Block139Part021SupportExplicit : Finset ℕ :=
  ([14033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block139Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14033
    = surrogateDiagTailX0RatChunk000Sub001Block139Part021

theorem surrogateDiagonalTailChunk000Sub001Block139Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part021] using hcert

def TailChunk000Sub001Block139Part022SupportExplicit : Finset ℕ :=
  ([14034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part022 : ℚ :=
  (341884367525 : ℚ) / 597715988644590144

def SurrogateDiagonalTailChunk000Sub001Block139Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14034
    = surrogateDiagTailX0RatChunk000Sub001Block139Part022

theorem surrogateDiagonalTailChunk000Sub001Block139Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part022] using hcert

def TailChunk000Sub001Block139Part023SupportExplicit : Finset ℕ :=
  ([14035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part023 : ℚ :=
  (31505016277 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk000Sub001Block139Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14035
    = surrogateDiagTailX0RatChunk000Sub001Block139Part023

theorem surrogateDiagonalTailChunk000Sub001Block139Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part023] using hcert

def TailChunk000Sub001Block139Part024SupportExplicit : Finset ℕ :=
  ([14037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block139Part024 : ℚ :=
  (684177660275 : ℚ) / 9579828090738767424

def SurrogateDiagonalTailChunk000Sub001Block139Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14037
    = surrogateDiagTailX0RatChunk000Sub001Block139Part024

theorem surrogateDiagonalTailChunk000Sub001Block139Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block139Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block139Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block139Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block139Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block139Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block139Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block139HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block139Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block139Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block139Part000
    + surrogateDiagTailX0RatChunk000Sub001Block139Part001
    + surrogateDiagTailX0RatChunk000Sub001Block139Part002
    + surrogateDiagTailX0RatChunk000Sub001Block139Part003
    + surrogateDiagTailX0RatChunk000Sub001Block139Part004
    + surrogateDiagTailX0RatChunk000Sub001Block139Part005
    + surrogateDiagTailX0RatChunk000Sub001Block139Part006
    + surrogateDiagTailX0RatChunk000Sub001Block139Part007
    + surrogateDiagTailX0RatChunk000Sub001Block139Part008
    + surrogateDiagTailX0RatChunk000Sub001Block139Part009

def surrogateDiagonalTailChunk000Sub001Block139MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block139Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block139Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block139Part010
    + surrogateDiagTailX0RatChunk000Sub001Block139Part011
    + surrogateDiagTailX0RatChunk000Sub001Block139Part012
    + surrogateDiagTailX0RatChunk000Sub001Block139Part013
    + surrogateDiagTailX0RatChunk000Sub001Block139Part014
    + surrogateDiagTailX0RatChunk000Sub001Block139Part015
    + surrogateDiagTailX0RatChunk000Sub001Block139Part016
    + surrogateDiagTailX0RatChunk000Sub001Block139Part017
    + surrogateDiagTailX0RatChunk000Sub001Block139Part018
    + surrogateDiagTailX0RatChunk000Sub001Block139Part019

def surrogateDiagonalTailChunk000Sub001Block139TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block139Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block139Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block139Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block139Part020
    + surrogateDiagTailX0RatChunk000Sub001Block139Part021
    + surrogateDiagTailX0RatChunk000Sub001Block139Part022
    + surrogateDiagTailX0RatChunk000Sub001Block139Part023
    + surrogateDiagTailX0RatChunk000Sub001Block139Part024

def surrogateDiagonalTailChunk000Sub001Block139Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block139HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block139MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block139TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block139 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block139Part000
    + surrogateDiagTailX0RatChunk000Sub001Block139Part001
    + surrogateDiagTailX0RatChunk000Sub001Block139Part002
    + surrogateDiagTailX0RatChunk000Sub001Block139Part003
    + surrogateDiagTailX0RatChunk000Sub001Block139Part004
    + surrogateDiagTailX0RatChunk000Sub001Block139Part005
    + surrogateDiagTailX0RatChunk000Sub001Block139Part006
    + surrogateDiagTailX0RatChunk000Sub001Block139Part007
    + surrogateDiagTailX0RatChunk000Sub001Block139Part008
    + surrogateDiagTailX0RatChunk000Sub001Block139Part009
    + surrogateDiagTailX0RatChunk000Sub001Block139Part010
    + surrogateDiagTailX0RatChunk000Sub001Block139Part011
    + surrogateDiagTailX0RatChunk000Sub001Block139Part012
    + surrogateDiagTailX0RatChunk000Sub001Block139Part013
    + surrogateDiagTailX0RatChunk000Sub001Block139Part014
    + surrogateDiagTailX0RatChunk000Sub001Block139Part015
    + surrogateDiagTailX0RatChunk000Sub001Block139Part016
    + surrogateDiagTailX0RatChunk000Sub001Block139Part017
    + surrogateDiagTailX0RatChunk000Sub001Block139Part018
    + surrogateDiagTailX0RatChunk000Sub001Block139Part019
    + surrogateDiagTailX0RatChunk000Sub001Block139Part020
    + surrogateDiagTailX0RatChunk000Sub001Block139Part021
    + surrogateDiagTailX0RatChunk000Sub001Block139Part022
    + surrogateDiagTailX0RatChunk000Sub001Block139Part023
    + surrogateDiagTailX0RatChunk000Sub001Block139Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block139_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block139Head + surrogateDiagTailX0RatChunk000Sub001Block139Mid + surrogateDiagTailX0RatChunk000Sub001Block139Tail =
      surrogateDiagTailX0RatChunk000Sub001Block139 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block139Head surrogateDiagTailX0RatChunk000Sub001Block139Mid surrogateDiagTailX0RatChunk000Sub001Block139Tail surrogateDiagTailX0RatChunk000Sub001Block139
  ring

def SurrogateDiagonalTailChunk000Sub001Block139HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block139HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block139Head

def SurrogateDiagonalTailChunk000Sub001Block139MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block139MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block139Mid

def SurrogateDiagonalTailChunk000Sub001Block139TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block139TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block139Tail

theorem surrogateDiagonalTailChunk000Sub001Block139_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block139HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block139MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block139TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block139Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block139 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block139HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block139MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block139TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block139Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block139_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

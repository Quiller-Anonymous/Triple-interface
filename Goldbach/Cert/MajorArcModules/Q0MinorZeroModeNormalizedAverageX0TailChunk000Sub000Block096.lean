import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [96,97). -/

/- Block 096 covers tail-support indices [2400,2425) and q from 3998 to 4037. -/

def TailChunk000Sub000Block096Part000SupportExplicit : Finset ℕ :=
  ([3998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part000 : ℚ :=
  (499400224975 : ℚ) / 39848207888008008

def SurrogateDiagonalTailChunk000Sub000Block096Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3998
    = surrogateDiagTailX0RatChunk000Sub000Block096Part000

theorem surrogateDiagonalTailChunk000Sub000Block096Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part000] using hcert

def TailChunk000Sub000Block096Part001SupportExplicit : Finset ℕ :=
  ([3999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part001 : ℚ :=
  (25561468291 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block096Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3999
    = surrogateDiagTailX0RatChunk000Sub000Block096Part001

theorem surrogateDiagonalTailChunk000Sub000Block096Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part001] using hcert

def TailChunk000Sub000Block096Part002SupportExplicit : Finset ℕ :=
  ([4001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part002 : ℚ :=
  (80023996999 : ℚ) / 25605120000000000

def SurrogateDiagonalTailChunk000Sub000Block096Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4001
    = surrogateDiagTailX0RatChunk000Sub000Block096Part002

theorem surrogateDiagonalTailChunk000Sub000Block096Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part002] using hcert

def TailChunk000Sub000Block096Part003SupportExplicit : Finset ℕ :=
  ([4002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part003 : ℚ :=
  (61769669575 : ℚ) / 822946590326784

def SurrogateDiagonalTailChunk000Sub000Block096Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4002
    = surrogateDiagTailX0RatChunk000Sub000Block096Part003

theorem surrogateDiagonalTailChunk000Sub000Block096Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part003] using hcert

def TailChunk000Sub000Block096Part004SupportExplicit : Finset ℕ :=
  ([4003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part004 : ℚ :=
  (2002600524775 : ℚ) / 641409216512104008

def SurrogateDiagonalTailChunk000Sub000Block096Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4003
    = surrogateDiagTailX0RatChunk000Sub000Block096Part004

theorem surrogateDiagonalTailChunk000Sub000Block096Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part004] using hcert

def TailChunk000Sub000Block096Part005SupportExplicit : Finset ℕ :=
  ([4006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part005 : ℚ :=
  (5115311475 : ℚ) / 273253552435864

def SurrogateDiagonalTailChunk000Sub000Block096Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4006
    = surrogateDiagTailX0RatChunk000Sub000Block096Part005

theorem surrogateDiagonalTailChunk000Sub000Block096Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part005] using hcert

def TailChunk000Sub000Block096Part006SupportExplicit : Finset ℕ :=
  ([4007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part006 : ℚ :=
  (2006604723775 : ℚ) / 643977418372968648

def SurrogateDiagonalTailChunk000Sub000Block096Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4007
    = surrogateDiagTailX0RatChunk000Sub000Block096Part006

theorem surrogateDiagonalTailChunk000Sub000Block096Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part006] using hcert

def TailChunk000Sub000Block096Part007SupportExplicit : Finset ℕ :=
  ([4009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part007 : ℚ :=
  (38487901351 : ℚ) / 20419920623491200

def SurrogateDiagonalTailChunk000Sub000Block096Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4009
    = surrogateDiagTailX0RatChunk000Sub000Block096Part007

theorem surrogateDiagonalTailChunk000Sub000Block096Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part007] using hcert

def TailChunk000Sub000Block096Part008SupportExplicit : Finset ℕ :=
  ([4010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part008 : ℚ :=
  (8626327031 : ℚ) / 327745536000000

def SurrogateDiagonalTailChunk000Sub000Block096Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4010
    = surrogateDiagTailX0RatChunk000Sub000Block096Part008

theorem surrogateDiagonalTailChunk000Sub000Block096Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part008] using hcert

def TailChunk000Sub000Block096Part009SupportExplicit : Finset ℕ :=
  ([4011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part009 : ℚ :=
  (540959027 : ℚ) / 54057534465024

def SurrogateDiagonalTailChunk000Sub000Block096Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4011
    = surrogateDiagTailX0RatChunk000Sub000Block096Part009

theorem surrogateDiagonalTailChunk000Sub000Block096Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part009] using hcert

def TailChunk000Sub000Block096Part010SupportExplicit : Finset ℕ :=
  ([4013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part010 : ℚ :=
  (251627640625 : ℚ) / 161961043024418592

def SurrogateDiagonalTailChunk000Sub000Block096Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4013
    = surrogateDiagTailX0RatChunk000Sub000Block096Part010

theorem surrogateDiagonalTailChunk000Sub000Block096Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part010] using hcert

def TailChunk000Sub000Block096Part011SupportExplicit : Finset ℕ :=
  ([4015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part011 : ℚ :=
  (10349026417 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub000Block096Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4015
    = surrogateDiagTailX0RatChunk000Sub000Block096Part011

theorem surrogateDiagonalTailChunk000Sub000Block096Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part011] using hcert

def TailChunk000Sub000Block096Part012SupportExplicit : Finset ℕ :=
  ([4017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part012 : ℚ :=
  (20024331175 : ℚ) / 2494422481379328

def SurrogateDiagonalTailChunk000Sub000Block096Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4017
    = surrogateDiagTailX0RatChunk000Sub000Block096Part012

theorem surrogateDiagonalTailChunk000Sub000Block096Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part012] using hcert

def TailChunk000Sub000Block096Part013SupportExplicit : Finset ℕ :=
  ([4019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part013 : ℚ :=
  (252380640625 : ℚ) / 162932078285287122

def SurrogateDiagonalTailChunk000Sub000Block096Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4019
    = surrogateDiagTailX0RatChunk000Sub000Block096Part013

theorem surrogateDiagonalTailChunk000Sub000Block096Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part013] using hcert

def TailChunk000Sub000Block096Part014SupportExplicit : Finset ℕ :=
  ([4021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part014 : ℚ :=
  (404211025 : ℚ) / 261210759865632

def SurrogateDiagonalTailChunk000Sub000Block096Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4021
    = surrogateDiagTailX0RatChunk000Sub000Block096Part014

theorem surrogateDiagonalTailChunk000Sub000Block096Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part014] using hcert

def TailChunk000Sub000Block096Part015SupportExplicit : Finset ℕ :=
  ([4022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part015 : ℚ :=
  (3368752793 : ℚ) / 181396361017800

def SurrogateDiagonalTailChunk000Sub000Block096Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4022
    = surrogateDiagTailX0RatChunk000Sub000Block096Part015

theorem surrogateDiagonalTailChunk000Sub000Block096Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part015] using hcert

def TailChunk000Sub000Block096Part016SupportExplicit : Finset ℕ :=
  ([4026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part016 : ℚ :=
  (88662127 : ℚ) / 1382676480000

def SurrogateDiagonalTailChunk000Sub000Block096Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4026
    = surrogateDiagTailX0RatChunk000Sub000Block096Part016

theorem surrogateDiagonalTailChunk000Sub000Block096Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part016] using hcert

def TailChunk000Sub000Block096Part017SupportExplicit : Finset ℕ :=
  ([4027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part017 : ℚ :=
  (253386390625 : ℚ) / 164233576192819122

def SurrogateDiagonalTailChunk000Sub000Block096Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4027
    = surrogateDiagTailX0RatChunk000Sub000Block096Part017

theorem surrogateDiagonalTailChunk000Sub000Block096Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part017] using hcert

def TailChunk000Sub000Block096Part018SupportExplicit : Finset ℕ :=
  ([4029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part018 : ℚ :=
  (736659448825 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub000Block096Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4029
    = surrogateDiagTailX0RatChunk000Sub000Block096Part018

theorem surrogateDiagonalTailChunk000Sub000Block096Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part018] using hcert

def TailChunk000Sub000Block096Part019SupportExplicit : Finset ℕ :=
  ([4030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part019 : ℚ :=
  (1059808223 : ℚ) / 28671179489280

def SurrogateDiagonalTailChunk000Sub000Block096Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4030
    = surrogateDiagTailX0RatChunk000Sub000Block096Part019

theorem surrogateDiagonalTailChunk000Sub000Block096Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part019] using hcert

def TailChunk000Sub000Block096Part020SupportExplicit : Finset ℕ :=
  ([4031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part020 : ℚ :=
  (12144179675 : ℚ) / 6881614035437568

def SurrogateDiagonalTailChunk000Sub000Block096Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4031
    = surrogateDiagTailX0RatChunk000Sub000Block096Part020

theorem surrogateDiagonalTailChunk000Sub000Block096Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part020] using hcert

def TailChunk000Sub000Block096Part021SupportExplicit : Finset ℕ :=
  ([4033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part021 : ℚ :=
  (1932988026625 : ℚ) / 571389011211091968

def SurrogateDiagonalTailChunk000Sub000Block096Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4033
    = surrogateDiagTailX0RatChunk000Sub000Block096Part021

theorem surrogateDiagonalTailChunk000Sub000Block096Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part021] using hcert

def TailChunk000Sub000Block096Part022SupportExplicit : Finset ℕ :=
  ([4034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part022 : ℚ :=
  (1729022825 : ℚ) / 93659186331648

def SurrogateDiagonalTailChunk000Sub000Block096Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4034
    = surrogateDiagTailX0RatChunk000Sub000Block096Part022

theorem surrogateDiagonalTailChunk000Sub000Block096Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part022] using hcert

def TailChunk000Sub000Block096Part023SupportExplicit : Finset ℕ :=
  ([4035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part023 : ℚ :=
  (841989636775 : ℚ) / 52835519625166848

def SurrogateDiagonalTailChunk000Sub000Block096Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4035
    = surrogateDiagTailX0RatChunk000Sub000Block096Part023

theorem surrogateDiagonalTailChunk000Sub000Block096Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part023] using hcert

def TailChunk000Sub000Block096Part024SupportExplicit : Finset ℕ :=
  ([4037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block096Part024 : ℚ :=
  (71131190941 : ℚ) / 17947798777987200

def SurrogateDiagonalTailChunk000Sub000Block096Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4037
    = surrogateDiagTailX0RatChunk000Sub000Block096Part024

theorem surrogateDiagonalTailChunk000Sub000Block096Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block096Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block096Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block096Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block096Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block096Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block096HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block096Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block096Part000
    + surrogateDiagTailX0RatChunk000Sub000Block096Part001
    + surrogateDiagTailX0RatChunk000Sub000Block096Part002
    + surrogateDiagTailX0RatChunk000Sub000Block096Part003
    + surrogateDiagTailX0RatChunk000Sub000Block096Part004
    + surrogateDiagTailX0RatChunk000Sub000Block096Part005
    + surrogateDiagTailX0RatChunk000Sub000Block096Part006
    + surrogateDiagTailX0RatChunk000Sub000Block096Part007
    + surrogateDiagTailX0RatChunk000Sub000Block096Part008
    + surrogateDiagTailX0RatChunk000Sub000Block096Part009

def surrogateDiagonalTailChunk000Sub000Block096MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block096Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block096Part010
    + surrogateDiagTailX0RatChunk000Sub000Block096Part011
    + surrogateDiagTailX0RatChunk000Sub000Block096Part012
    + surrogateDiagTailX0RatChunk000Sub000Block096Part013
    + surrogateDiagTailX0RatChunk000Sub000Block096Part014
    + surrogateDiagTailX0RatChunk000Sub000Block096Part015
    + surrogateDiagTailX0RatChunk000Sub000Block096Part016
    + surrogateDiagTailX0RatChunk000Sub000Block096Part017
    + surrogateDiagTailX0RatChunk000Sub000Block096Part018
    + surrogateDiagTailX0RatChunk000Sub000Block096Part019

def surrogateDiagonalTailChunk000Sub000Block096TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block096Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block096Part020
    + surrogateDiagTailX0RatChunk000Sub000Block096Part021
    + surrogateDiagTailX0RatChunk000Sub000Block096Part022
    + surrogateDiagTailX0RatChunk000Sub000Block096Part023
    + surrogateDiagTailX0RatChunk000Sub000Block096Part024

def surrogateDiagonalTailChunk000Sub000Block096Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block096HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block096MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block096TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block096 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block096Part000
    + surrogateDiagTailX0RatChunk000Sub000Block096Part001
    + surrogateDiagTailX0RatChunk000Sub000Block096Part002
    + surrogateDiagTailX0RatChunk000Sub000Block096Part003
    + surrogateDiagTailX0RatChunk000Sub000Block096Part004
    + surrogateDiagTailX0RatChunk000Sub000Block096Part005
    + surrogateDiagTailX0RatChunk000Sub000Block096Part006
    + surrogateDiagTailX0RatChunk000Sub000Block096Part007
    + surrogateDiagTailX0RatChunk000Sub000Block096Part008
    + surrogateDiagTailX0RatChunk000Sub000Block096Part009
    + surrogateDiagTailX0RatChunk000Sub000Block096Part010
    + surrogateDiagTailX0RatChunk000Sub000Block096Part011
    + surrogateDiagTailX0RatChunk000Sub000Block096Part012
    + surrogateDiagTailX0RatChunk000Sub000Block096Part013
    + surrogateDiagTailX0RatChunk000Sub000Block096Part014
    + surrogateDiagTailX0RatChunk000Sub000Block096Part015
    + surrogateDiagTailX0RatChunk000Sub000Block096Part016
    + surrogateDiagTailX0RatChunk000Sub000Block096Part017
    + surrogateDiagTailX0RatChunk000Sub000Block096Part018
    + surrogateDiagTailX0RatChunk000Sub000Block096Part019
    + surrogateDiagTailX0RatChunk000Sub000Block096Part020
    + surrogateDiagTailX0RatChunk000Sub000Block096Part021
    + surrogateDiagTailX0RatChunk000Sub000Block096Part022
    + surrogateDiagTailX0RatChunk000Sub000Block096Part023
    + surrogateDiagTailX0RatChunk000Sub000Block096Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block096_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block096Head + surrogateDiagTailX0RatChunk000Sub000Block096Mid + surrogateDiagTailX0RatChunk000Sub000Block096Tail =
      surrogateDiagTailX0RatChunk000Sub000Block096 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block096Head surrogateDiagTailX0RatChunk000Sub000Block096Mid surrogateDiagTailX0RatChunk000Sub000Block096Tail surrogateDiagTailX0RatChunk000Sub000Block096
  ring

def SurrogateDiagonalTailChunk000Sub000Block096HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block096HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block096Head

def SurrogateDiagonalTailChunk000Sub000Block096MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block096MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block096Mid

def SurrogateDiagonalTailChunk000Sub000Block096TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block096TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block096Tail

theorem surrogateDiagonalTailChunk000Sub000Block096_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block096HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block096MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block096TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block096Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block096 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block096HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block096MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block096TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block096Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block096_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [126,127). -/

/- Block 126 covers tail-support indices [3150,3175) and q from 5233 to 5273. -/

def TailChunk000Sub000Block126Part000SupportExplicit : Finset ℕ :=
  ([5233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part000 : ℚ :=
  (427879515625 : ℚ) / 468422566019407872

def SurrogateDiagonalTailChunk000Sub000Block126Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5233
    = surrogateDiagTailX0RatChunk000Sub000Block126Part000

theorem surrogateDiagonalTailChunk000Sub000Block126Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part000] using hcert

def TailChunk000Sub000Block126Part001SupportExplicit : Finset ℕ :=
  ([5234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part001 : ℚ :=
  (107010765625 : ℚ) / 29276410376212992

def SurrogateDiagonalTailChunk000Sub000Block126Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5234
    = surrogateDiagTailX0RatChunk000Sub000Block126Part001

theorem surrogateDiagonalTailChunk000Sub000Block126Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part001] using hcert

def TailChunk000Sub000Block126Part002SupportExplicit : Finset ℕ :=
  ([5235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part002 : ℚ :=
  (301127630575 : ℚ) / 50070569136685056

def SurrogateDiagonalTailChunk000Sub000Block126Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5235
    = surrogateDiagTailX0RatChunk000Sub000Block126Part002

theorem surrogateDiagonalTailChunk000Sub000Block126Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part002] using hcert

def TailChunk000Sub000Block126Part003SupportExplicit : Finset ℕ :=
  ([5237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part003 : ℚ :=
  (428533890625 : ℚ) / 469856694526155552

def SurrogateDiagonalTailChunk000Sub000Block126Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5237
    = surrogateDiagTailX0RatChunk000Sub000Block126Part003

theorem surrogateDiagonalTailChunk000Sub000Block126Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part003] using hcert

def TailChunk000Sub000Block126Part004SupportExplicit : Finset ℕ :=
  ([5241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part004 : ℚ :=
  (38127275 : ℚ) / 12391266403008

def SurrogateDiagonalTailChunk000Sub000Block126Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5241
    = surrogateDiagTailX0RatChunk000Sub000Block126Part004

theorem surrogateDiagonalTailChunk000Sub000Block126Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part004] using hcert

def TailChunk000Sub000Block126Part005SupportExplicit : Finset ℕ :=
  ([5242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part005 : ℚ :=
  (34341335359 : ℚ) / 4712941135747200

def SurrogateDiagonalTailChunk000Sub000Block126Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5242
    = surrogateDiagTailX0RatChunk000Sub000Block126Part005

theorem surrogateDiagonalTailChunk000Sub000Block126Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part005] using hcert

def TailChunk000Sub000Block126Part006SupportExplicit : Finset ℕ :=
  ([5245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part006 : ℚ :=
  (687202287875 : ℚ) / 386084137840410624

def SurrogateDiagonalTailChunk000Sub000Block126Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5245
    = surrogateDiagTailX0RatChunk000Sub000Block126Part006

theorem surrogateDiagonalTailChunk000Sub000Block126Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part006] using hcert

def TailChunk000Sub000Block126Part007SupportExplicit : Finset ℕ :=
  ([5246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part007 : ℚ :=
  (16498867667 : ℚ) / 2016782283801600

def SurrogateDiagonalTailChunk000Sub000Block126Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5246
    = surrogateDiagTailX0RatChunk000Sub000Block126Part007

theorem surrogateDiagonalTailChunk000Sub000Block126Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part007] using hcert

def TailChunk000Sub000Block126Part008SupportExplicit : Finset ℕ :=
  ([5249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part008 : ℚ :=
  (13210270763 : ℚ) / 12907406616330240

def SurrogateDiagonalTailChunk000Sub000Block126Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5249
    = surrogateDiagTailX0RatChunk000Sub000Block126Part008

theorem surrogateDiagonalTailChunk000Sub000Block126Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part008] using hcert

def TailChunk000Sub000Block126Part009SupportExplicit : Finset ℕ :=
  ([5251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part009 : ℚ :=
  (836789531375 : ℚ) / 848475929085886464

def SurrogateDiagonalTailChunk000Sub000Block126Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5251
    = surrogateDiagTailX0RatChunk000Sub000Block126Part009

theorem surrogateDiagonalTailChunk000Sub000Block126Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part009] using hcert

def TailChunk000Sub000Block126Part010SupportExplicit : Finset ℕ :=
  ([5253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part010 : ℚ :=
  (35573375 : ℚ) / 9458436538368

def SurrogateDiagonalTailChunk000Sub000Block126Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5253
    = surrogateDiagTailX0RatChunk000Sub000Block126Part010

theorem surrogateDiagonalTailChunk000Sub000Block126Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part010] using hcert

def TailChunk000Sub000Block126Part011SupportExplicit : Finset ℕ :=
  ([5254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part011 : ℚ :=
  (4719211219 : ℚ) / 576223509657600

def SurrogateDiagonalTailChunk000Sub000Block126Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5254
    = surrogateDiagTailX0RatChunk000Sub000Block126Part011

theorem surrogateDiagonalTailChunk000Sub000Block126Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part011] using hcert

def TailChunk000Sub000Block126Part012SupportExplicit : Finset ℕ :=
  ([5255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part012 : ℚ :=
  (5518602499 : ℚ) / 3112318339200000

def SurrogateDiagonalTailChunk000Sub000Block126Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5255
    = surrogateDiagTailX0RatChunk000Sub000Block126Part012

theorem surrogateDiagonalTailChunk000Sub000Block126Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part012] using hcert

def TailChunk000Sub000Block126Part013SupportExplicit : Finset ℕ :=
  ([5257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part013 : ℚ :=
  (219071111 : ℚ) / 151905375000000

def SurrogateDiagonalTailChunk000Sub000Block126Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5257
    = surrogateDiagTailX0RatChunk000Sub000Block126Part013

theorem surrogateDiagonalTailChunk000Sub000Block126Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part013] using hcert

def TailChunk000Sub000Block126Part014SupportExplicit : Finset ℕ :=
  ([5258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part014 : ℚ :=
  (2583469731 : ℚ) / 267432037045600

def SurrogateDiagonalTailChunk000Sub000Block126Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5258
    = surrogateDiagTailX0RatChunk000Sub000Block126Part014

theorem surrogateDiagonalTailChunk000Sub000Block126Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part014] using hcert

def TailChunk000Sub000Block126Part015SupportExplicit : Finset ℕ :=
  ([5259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part015 : ℚ :=
  (38389625 : ℚ) / 12562473074688

def SurrogateDiagonalTailChunk000Sub000Block126Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5259
    = surrogateDiagTailX0RatChunk000Sub000Block126Part015

theorem surrogateDiagonalTailChunk000Sub000Block126Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part015] using hcert

def TailChunk000Sub000Block126Part016SupportExplicit : Finset ℕ :=
  ([5261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block126Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5261
    = surrogateDiagTailX0RatChunk000Sub000Block126Part016

theorem surrogateDiagonalTailChunk000Sub000Block126Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part016] using hcert

def TailChunk000Sub000Block126Part017SupportExplicit : Finset ℕ :=
  ([5262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part017 : ℚ :=
  (384351031075 : ℚ) / 23559347942443008

def SurrogateDiagonalTailChunk000Sub000Block126Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5262
    = surrogateDiagTailX0RatChunk000Sub000Block126Part017

theorem surrogateDiagonalTailChunk000Sub000Block126Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part017] using hcert

def TailChunk000Sub000Block126Part018SupportExplicit : Finset ℕ :=
  ([5263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part018 : ℚ :=
  (22756689925 : ℚ) / 380796735173571072

def SurrogateDiagonalTailChunk000Sub000Block126Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5263
    = surrogateDiagTailX0RatChunk000Sub000Block126Part018

theorem surrogateDiagonalTailChunk000Sub000Block126Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part018] using hcert

def TailChunk000Sub000Block126Part019SupportExplicit : Finset ℕ :=
  ([5266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part019 : ℚ :=
  (866412807775 : ℚ) / 119997002791077888

def SurrogateDiagonalTailChunk000Sub000Block126Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5266
    = surrogateDiagTailX0RatChunk000Sub000Block126Part019

theorem surrogateDiagonalTailChunk000Sub000Block126Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part019] using hcert

def TailChunk000Sub000Block126Part020SupportExplicit : Finset ℕ :=
  ([5267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part020 : ℚ :=
  (1647905488825 : ℚ) / 1582912724204832768

def SurrogateDiagonalTailChunk000Sub000Block126Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5267
    = surrogateDiagTailX0RatChunk000Sub000Block126Part020

theorem surrogateDiagonalTailChunk000Sub000Block126Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part020] using hcert

def TailChunk000Sub000Block126Part021SupportExplicit : Finset ℕ :=
  ([5269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part021 : ℚ :=
  (3148526579 : ℚ) / 2610768962182560

def SurrogateDiagonalTailChunk000Sub000Block126Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5269
    = surrogateDiagTailX0RatChunk000Sub000Block126Part021

theorem surrogateDiagonalTailChunk000Sub000Block126Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part021] using hcert

def TailChunk000Sub000Block126Part022SupportExplicit : Finset ℕ :=
  ([5270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part022 : ℚ :=
  (12602771609 : ℚ) / 679613143449600

def SurrogateDiagonalTailChunk000Sub000Block126Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5270
    = surrogateDiagTailX0RatChunk000Sub000Block126Part022

theorem surrogateDiagonalTailChunk000Sub000Block126Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part022] using hcert

def TailChunk000Sub000Block126Part023SupportExplicit : Finset ℕ :=
  ([5271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part023 : ℚ :=
  (38750804617 : ℚ) / 8101620000000000

def SurrogateDiagonalTailChunk000Sub000Block126Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5271
    = surrogateDiagTailX0RatChunk000Sub000Block126Part023

theorem surrogateDiagonalTailChunk000Sub000Block126Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part023] using hcert

def TailChunk000Sub000Block126Part024SupportExplicit : Finset ℕ :=
  ([5273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block126Part024 : ℚ :=
  (434445765625 : ℚ) / 482912529813484032

def SurrogateDiagonalTailChunk000Sub000Block126Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5273
    = surrogateDiagTailX0RatChunk000Sub000Block126Part024

theorem surrogateDiagonalTailChunk000Sub000Block126Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block126Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block126Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block126Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block126Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block126Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block126HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block126Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block126Part000
    + surrogateDiagTailX0RatChunk000Sub000Block126Part001
    + surrogateDiagTailX0RatChunk000Sub000Block126Part002
    + surrogateDiagTailX0RatChunk000Sub000Block126Part003
    + surrogateDiagTailX0RatChunk000Sub000Block126Part004
    + surrogateDiagTailX0RatChunk000Sub000Block126Part005
    + surrogateDiagTailX0RatChunk000Sub000Block126Part006
    + surrogateDiagTailX0RatChunk000Sub000Block126Part007
    + surrogateDiagTailX0RatChunk000Sub000Block126Part008
    + surrogateDiagTailX0RatChunk000Sub000Block126Part009

def surrogateDiagonalTailChunk000Sub000Block126MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block126Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block126Part010
    + surrogateDiagTailX0RatChunk000Sub000Block126Part011
    + surrogateDiagTailX0RatChunk000Sub000Block126Part012
    + surrogateDiagTailX0RatChunk000Sub000Block126Part013
    + surrogateDiagTailX0RatChunk000Sub000Block126Part014
    + surrogateDiagTailX0RatChunk000Sub000Block126Part015
    + surrogateDiagTailX0RatChunk000Sub000Block126Part016
    + surrogateDiagTailX0RatChunk000Sub000Block126Part017
    + surrogateDiagTailX0RatChunk000Sub000Block126Part018
    + surrogateDiagTailX0RatChunk000Sub000Block126Part019

def surrogateDiagonalTailChunk000Sub000Block126TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block126Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block126Part020
    + surrogateDiagTailX0RatChunk000Sub000Block126Part021
    + surrogateDiagTailX0RatChunk000Sub000Block126Part022
    + surrogateDiagTailX0RatChunk000Sub000Block126Part023
    + surrogateDiagTailX0RatChunk000Sub000Block126Part024

def surrogateDiagonalTailChunk000Sub000Block126Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block126HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block126MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block126TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block126 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block126Part000
    + surrogateDiagTailX0RatChunk000Sub000Block126Part001
    + surrogateDiagTailX0RatChunk000Sub000Block126Part002
    + surrogateDiagTailX0RatChunk000Sub000Block126Part003
    + surrogateDiagTailX0RatChunk000Sub000Block126Part004
    + surrogateDiagTailX0RatChunk000Sub000Block126Part005
    + surrogateDiagTailX0RatChunk000Sub000Block126Part006
    + surrogateDiagTailX0RatChunk000Sub000Block126Part007
    + surrogateDiagTailX0RatChunk000Sub000Block126Part008
    + surrogateDiagTailX0RatChunk000Sub000Block126Part009
    + surrogateDiagTailX0RatChunk000Sub000Block126Part010
    + surrogateDiagTailX0RatChunk000Sub000Block126Part011
    + surrogateDiagTailX0RatChunk000Sub000Block126Part012
    + surrogateDiagTailX0RatChunk000Sub000Block126Part013
    + surrogateDiagTailX0RatChunk000Sub000Block126Part014
    + surrogateDiagTailX0RatChunk000Sub000Block126Part015
    + surrogateDiagTailX0RatChunk000Sub000Block126Part016
    + surrogateDiagTailX0RatChunk000Sub000Block126Part017
    + surrogateDiagTailX0RatChunk000Sub000Block126Part018
    + surrogateDiagTailX0RatChunk000Sub000Block126Part019
    + surrogateDiagTailX0RatChunk000Sub000Block126Part020
    + surrogateDiagTailX0RatChunk000Sub000Block126Part021
    + surrogateDiagTailX0RatChunk000Sub000Block126Part022
    + surrogateDiagTailX0RatChunk000Sub000Block126Part023
    + surrogateDiagTailX0RatChunk000Sub000Block126Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block126_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block126Head + surrogateDiagTailX0RatChunk000Sub000Block126Mid + surrogateDiagTailX0RatChunk000Sub000Block126Tail =
      surrogateDiagTailX0RatChunk000Sub000Block126 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block126Head surrogateDiagTailX0RatChunk000Sub000Block126Mid surrogateDiagTailX0RatChunk000Sub000Block126Tail surrogateDiagTailX0RatChunk000Sub000Block126
  ring

def SurrogateDiagonalTailChunk000Sub000Block126HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block126HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block126Head

def SurrogateDiagonalTailChunk000Sub000Block126MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block126MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block126Mid

def SurrogateDiagonalTailChunk000Sub000Block126TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block126TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block126Tail

theorem surrogateDiagonalTailChunk000Sub000Block126_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block126HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block126MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block126TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block126Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block126 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block126HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block126MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block126TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block126Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block126_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [99,100). -/

/- Block 099 covers tail-support indices [2475,2500) and q from 4121 to 4161. -/

def TailChunk000Sub000Block099Part000SupportExplicit : Finset ℕ :=
  ([4121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part000 : ℚ :=
  (249062593675 : ℚ) / 129252866142707712

def SurrogateDiagonalTailChunk000Sub000Block099Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4121
    = surrogateDiagTailX0RatChunk000Sub000Block099Part000

theorem surrogateDiagonalTailChunk000Sub000Block099Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part000] using hcert

def TailChunk000Sub000Block099Part001SupportExplicit : Finset ℕ :=
  ([4123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part001 : ℚ :=
  (35452096111 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block099Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4123
    = surrogateDiagTailX0RatChunk000Sub000Block099Part001

theorem surrogateDiagonalTailChunk000Sub000Block099Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part001] using hcert

def TailChunk000Sub000Block099Part002SupportExplicit : Finset ℕ :=
  ([4126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part002 : ℚ :=
  (531889725775 : ℚ) / 45204482589540168

def SurrogateDiagonalTailChunk000Sub000Block099Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4126
    = surrogateDiagTailX0RatChunk000Sub000Block099Part002

theorem surrogateDiagonalTailChunk000Sub000Block099Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part002] using hcert

def TailChunk000Sub000Block099Part003SupportExplicit : Finset ℕ :=
  ([4127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part003 : ℚ :=
  (266127015625 : ℚ) / 181168947833867922

def SurrogateDiagonalTailChunk000Sub000Block099Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4127
    = surrogateDiagTailX0RatChunk000Sub000Block099Part003

theorem surrogateDiagonalTailChunk000Sub000Block099Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part003] using hcert

def TailChunk000Sub000Block099Part004SupportExplicit : Finset ℕ :=
  ([4129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part004 : ℚ :=
  (266385015625 : ℚ) / 181520476128018432

def SurrogateDiagonalTailChunk000Sub000Block099Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4129
    = surrogateDiagTailX0RatChunk000Sub000Block099Part004

theorem surrogateDiagonalTailChunk000Sub000Block099Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part004] using hcert

def TailChunk000Sub000Block099Part005SupportExplicit : Finset ℕ :=
  ([4130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part005 : ℚ :=
  (388013435875 : ℚ) / 9388231713128448

def SurrogateDiagonalTailChunk000Sub000Block099Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4130
    = surrogateDiagTailX0RatChunk000Sub000Block099Part005

theorem surrogateDiagonalTailChunk000Sub000Block099Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part005] using hcert

def TailChunk000Sub000Block099Part006SupportExplicit : Finset ℕ :=
  ([4133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part006 : ℚ :=
  (2134784082775 : ℚ) / 728900268612981888

def SurrogateDiagonalTailChunk000Sub000Block099Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4133
    = surrogateDiagTailX0RatChunk000Sub000Block099Part006

theorem surrogateDiagonalTailChunk000Sub000Block099Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part006] using hcert

def TailChunk000Sub000Block099Part007SupportExplicit : Finset ℕ :=
  ([4134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part007 : ℚ :=
  (142119001925 : ℚ) / 2021919894798336

def SurrogateDiagonalTailChunk000Sub000Block099Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4134
    = surrogateDiagTailX0RatChunk000Sub000Block099Part007

theorem surrogateDiagonalTailChunk000Sub000Block099Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part007] using hcert

def TailChunk000Sub000Block099Part008SupportExplicit : Finset ℕ :=
  ([4135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part008 : ℚ :=
  (768270284375 : ℚ) / 148989964890891264

def SurrogateDiagonalTailChunk000Sub000Block099Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4135
    = surrogateDiagTailX0RatChunk000Sub000Block099Part008

theorem surrogateDiagonalTailChunk000Sub000Block099Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part008] using hcert

def TailChunk000Sub000Block099Part009SupportExplicit : Finset ℕ :=
  ([4137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part009 : ℚ :=
  (3958049925 : ℚ) / 314897965613056

def SurrogateDiagonalTailChunk000Sub000Block099Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4137
    = surrogateDiagTailX0RatChunk000Sub000Block099Part009

theorem surrogateDiagonalTailChunk000Sub000Block099Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part009] using hcert

def TailChunk000Sub000Block099Part010SupportExplicit : Finset ℕ :=
  ([4138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part010 : ℚ :=
  (267440543475 : ℚ) / 15244308949952896

def SurrogateDiagonalTailChunk000Sub000Block099Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4138
    = surrogateDiagTailX0RatChunk000Sub000Block099Part010

theorem surrogateDiagonalTailChunk000Sub000Block099Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part010] using hcert

def TailChunk000Sub000Block099Part011SupportExplicit : Finset ℕ :=
  ([4139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part011 : ℚ :=
  (2140986841975 : ℚ) / 733143188882752968

def SurrogateDiagonalTailChunk000Sub000Block099Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4139
    = surrogateDiagTailX0RatChunk000Sub000Block099Part011

theorem surrogateDiagonalTailChunk000Sub000Block099Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part011] using hcert

def TailChunk000Sub000Block099Part012SupportExplicit : Finset ℕ :=
  ([4141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part012 : ℚ :=
  (8345801033 : ℚ) / 5121024000000000

def SurrogateDiagonalTailChunk000Sub000Block099Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4141
    = surrogateDiagTailX0RatChunk000Sub000Block099Part012

theorem surrogateDiagonalTailChunk000Sub000Block099Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part012] using hcert

def TailChunk000Sub000Block099Part013SupportExplicit : Finset ℕ :=
  ([4142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part013 : ℚ :=
  (510139216525 : ℚ) / 35711813200693248

def SurrogateDiagonalTailChunk000Sub000Block099Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4142
    = surrogateDiagTailX0RatChunk000Sub000Block099Part013

theorem surrogateDiagonalTailChunk000Sub000Block099Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part013] using hcert

def TailChunk000Sub000Block099Part014SupportExplicit : Finset ℕ :=
  ([4143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part014 : ℚ :=
  (953033 : ℚ) / 193426099200

def SurrogateDiagonalTailChunk000Sub000Block099Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4143
    = surrogateDiagTailX0RatChunk000Sub000Block099Part014

theorem surrogateDiagonalTailChunk000Sub000Block099Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part014] using hcert

def TailChunk000Sub000Block099Part015SupportExplicit : Finset ℕ :=
  ([4145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part015 : ℚ :=
  (901250229625 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub000Block099Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4145
    = surrogateDiagTailX0RatChunk000Sub000Block099Part015

theorem surrogateDiagonalTailChunk000Sub000Block099Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part015] using hcert

def TailChunk000Sub000Block099Part016SupportExplicit : Finset ℕ :=
  ([4146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part016 : ℚ :=
  (168490037 : ℚ) / 3942896421600

def SurrogateDiagonalTailChunk000Sub000Block099Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4146
    = surrogateDiagTailX0RatChunk000Sub000Block099Part016

theorem surrogateDiagonalTailChunk000Sub000Block099Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part016] using hcert

def TailChunk000Sub000Block099Part017SupportExplicit : Finset ℕ :=
  ([4147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part017 : ℚ :=
  (18148531529 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub000Block099Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4147
    = surrogateDiagTailX0RatChunk000Sub000Block099Part017

theorem surrogateDiagonalTailChunk000Sub000Block099Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part017] using hcert

def TailChunk000Sub000Block099Part018SupportExplicit : Finset ℕ :=
  ([4151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part018 : ℚ :=
  (235982036875 : ℚ) / 99508160042237952

def SurrogateDiagonalTailChunk000Sub000Block099Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4151
    = surrogateDiagTailX0RatChunk000Sub000Block099Part018

theorem surrogateDiagonalTailChunk000Sub000Block099Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part018] using hcert

def TailChunk000Sub000Block099Part019SupportExplicit : Finset ℕ :=
  ([4153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part019 : ℚ :=
  (269490765625 : ℚ) / 185778840040100352

def SurrogateDiagonalTailChunk000Sub000Block099Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4153
    = surrogateDiagTailX0RatChunk000Sub000Block099Part019

theorem surrogateDiagonalTailChunk000Sub000Block099Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part019] using hcert

def TailChunk000Sub000Block099Part020SupportExplicit : Finset ℕ :=
  ([4154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part020 : ℚ :=
  (7639967893 : ℚ) / 384315251680800

def SurrogateDiagonalTailChunk000Sub000Block099Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4154
    = surrogateDiagTailX0RatChunk000Sub000Block099Part020

theorem surrogateDiagonalTailChunk000Sub000Block099Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part020] using hcert

def TailChunk000Sub000Block099Part021SupportExplicit : Finset ℕ :=
  ([4155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part021 : ℚ :=
  (37656170275 : ℚ) / 3714523860860928

def SurrogateDiagonalTailChunk000Sub000Block099Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4155
    = surrogateDiagTailX0RatChunk000Sub000Block099Part021

theorem surrogateDiagonalTailChunk000Sub000Block099Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part021] using hcert

def TailChunk000Sub000Block099Part022SupportExplicit : Finset ℕ :=
  ([4157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part022 : ℚ :=
  (270010140625 : ℚ) / 186495786009422112

def SurrogateDiagonalTailChunk000Sub000Block099Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4157
    = surrogateDiagTailX0RatChunk000Sub000Block099Part022

theorem surrogateDiagonalTailChunk000Sub000Block099Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part022] using hcert

def TailChunk000Sub000Block099Part023SupportExplicit : Finset ℕ :=
  ([4159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part023 : ℚ :=
  (270270015625 : ℚ) / 186855036155334162

def SurrogateDiagonalTailChunk000Sub000Block099Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4159
    = surrogateDiagTailX0RatChunk000Sub000Block099Part023

theorem surrogateDiagonalTailChunk000Sub000Block099Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part023] using hcert

def TailChunk000Sub000Block099Part024SupportExplicit : Finset ℕ :=
  ([4161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block099Part024 : ℚ :=
  (43735101325 : ℚ) / 6270386954305536

def SurrogateDiagonalTailChunk000Sub000Block099Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4161
    = surrogateDiagTailX0RatChunk000Sub000Block099Part024

theorem surrogateDiagonalTailChunk000Sub000Block099Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block099Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block099Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block099Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block099Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block099Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block099HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block099Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block099Part000
    + surrogateDiagTailX0RatChunk000Sub000Block099Part001
    + surrogateDiagTailX0RatChunk000Sub000Block099Part002
    + surrogateDiagTailX0RatChunk000Sub000Block099Part003
    + surrogateDiagTailX0RatChunk000Sub000Block099Part004
    + surrogateDiagTailX0RatChunk000Sub000Block099Part005
    + surrogateDiagTailX0RatChunk000Sub000Block099Part006
    + surrogateDiagTailX0RatChunk000Sub000Block099Part007
    + surrogateDiagTailX0RatChunk000Sub000Block099Part008
    + surrogateDiagTailX0RatChunk000Sub000Block099Part009

def surrogateDiagonalTailChunk000Sub000Block099MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block099Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block099Part010
    + surrogateDiagTailX0RatChunk000Sub000Block099Part011
    + surrogateDiagTailX0RatChunk000Sub000Block099Part012
    + surrogateDiagTailX0RatChunk000Sub000Block099Part013
    + surrogateDiagTailX0RatChunk000Sub000Block099Part014
    + surrogateDiagTailX0RatChunk000Sub000Block099Part015
    + surrogateDiagTailX0RatChunk000Sub000Block099Part016
    + surrogateDiagTailX0RatChunk000Sub000Block099Part017
    + surrogateDiagTailX0RatChunk000Sub000Block099Part018
    + surrogateDiagTailX0RatChunk000Sub000Block099Part019

def surrogateDiagonalTailChunk000Sub000Block099TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block099Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block099Part020
    + surrogateDiagTailX0RatChunk000Sub000Block099Part021
    + surrogateDiagTailX0RatChunk000Sub000Block099Part022
    + surrogateDiagTailX0RatChunk000Sub000Block099Part023
    + surrogateDiagTailX0RatChunk000Sub000Block099Part024

def surrogateDiagonalTailChunk000Sub000Block099Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block099HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block099MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block099TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block099 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block099Part000
    + surrogateDiagTailX0RatChunk000Sub000Block099Part001
    + surrogateDiagTailX0RatChunk000Sub000Block099Part002
    + surrogateDiagTailX0RatChunk000Sub000Block099Part003
    + surrogateDiagTailX0RatChunk000Sub000Block099Part004
    + surrogateDiagTailX0RatChunk000Sub000Block099Part005
    + surrogateDiagTailX0RatChunk000Sub000Block099Part006
    + surrogateDiagTailX0RatChunk000Sub000Block099Part007
    + surrogateDiagTailX0RatChunk000Sub000Block099Part008
    + surrogateDiagTailX0RatChunk000Sub000Block099Part009
    + surrogateDiagTailX0RatChunk000Sub000Block099Part010
    + surrogateDiagTailX0RatChunk000Sub000Block099Part011
    + surrogateDiagTailX0RatChunk000Sub000Block099Part012
    + surrogateDiagTailX0RatChunk000Sub000Block099Part013
    + surrogateDiagTailX0RatChunk000Sub000Block099Part014
    + surrogateDiagTailX0RatChunk000Sub000Block099Part015
    + surrogateDiagTailX0RatChunk000Sub000Block099Part016
    + surrogateDiagTailX0RatChunk000Sub000Block099Part017
    + surrogateDiagTailX0RatChunk000Sub000Block099Part018
    + surrogateDiagTailX0RatChunk000Sub000Block099Part019
    + surrogateDiagTailX0RatChunk000Sub000Block099Part020
    + surrogateDiagTailX0RatChunk000Sub000Block099Part021
    + surrogateDiagTailX0RatChunk000Sub000Block099Part022
    + surrogateDiagTailX0RatChunk000Sub000Block099Part023
    + surrogateDiagTailX0RatChunk000Sub000Block099Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block099_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block099Head + surrogateDiagTailX0RatChunk000Sub000Block099Mid + surrogateDiagTailX0RatChunk000Sub000Block099Tail =
      surrogateDiagTailX0RatChunk000Sub000Block099 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block099Head surrogateDiagTailX0RatChunk000Sub000Block099Mid surrogateDiagTailX0RatChunk000Sub000Block099Tail surrogateDiagTailX0RatChunk000Sub000Block099
  ring

def SurrogateDiagonalTailChunk000Sub000Block099HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block099HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block099Head

def SurrogateDiagonalTailChunk000Sub000Block099MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block099MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block099Mid

def SurrogateDiagonalTailChunk000Sub000Block099TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block099TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block099Tail

theorem surrogateDiagonalTailChunk000Sub000Block099_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block099HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block099MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block099TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block099Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block099 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block099HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block099MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block099TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block099Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block099_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

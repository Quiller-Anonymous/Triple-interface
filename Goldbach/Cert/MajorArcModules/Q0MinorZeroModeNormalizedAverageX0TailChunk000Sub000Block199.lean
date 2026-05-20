import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [199,200). -/

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

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [30,31). -/

/- Block 030 covers tail-support indices [750,775) and q from 1285 to 1321. -/

def TailChunk000Sub000Block030Part000SupportExplicit : Finset ℕ :=
  ([1285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part000 : ℚ :=
  (10976265225 : ℚ) / 114555367718912

def SurrogateDiagonalTailChunk000Sub000Block030Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1285
    = surrogateDiagTailX0RatChunk000Sub000Block030Part000

theorem surrogateDiagonalTailChunk000Sub000Block030Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part000] using hcert

def TailChunk000Sub000Block030Part001SupportExplicit : Finset ℕ :=
  ([1286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part001 : ℚ :=
  (51608771425 : ℚ) / 106195711705362

def SurrogateDiagonalTailChunk000Sub000Block030Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1286
    = surrogateDiagTailX0RatChunk000Sub000Block030Part001

theorem surrogateDiagonalTailChunk000Sub000Block030Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part001] using hcert

def TailChunk000Sub000Block030Part002SupportExplicit : Finset ℕ :=
  ([1289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part002 : ℚ :=
  (207565510925 : ℚ) / 3440807017718784

def SurrogateDiagonalTailChunk000Sub000Block030Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1289
    = surrogateDiagTailX0RatChunk000Sub000Block030Part002

theorem surrogateDiagonalTailChunk000Sub000Block030Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part002] using hcert

def TailChunk000Sub000Block030Part003SupportExplicit : Finset ℕ :=
  ([1290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part003 : ℚ :=
  (5612541475 : ℚ) / 1770563321856

def SurrogateDiagonalTailChunk000Sub000Block030Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1290
    = surrogateDiagTailX0RatChunk000Sub000Block030Part003

theorem surrogateDiagonalTailChunk000Sub000Block030Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part003] using hcert

def TailChunk000Sub000Block030Part004SupportExplicit : Finset ℕ :=
  ([1291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part004 : ℚ :=
  (8328404957 : ℚ) / 138489132788100

def SurrogateDiagonalTailChunk000Sub000Block030Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1291
    = surrogateDiagTailX0RatChunk000Sub000Block030Part004

theorem surrogateDiagonalTailChunk000Sub000Block030Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part004] using hcert

def TailChunk000Sub000Block030Part005SupportExplicit : Finset ℕ :=
  ([1293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part005 : ℚ :=
  (10658735959 : ℚ) / 54711756163200

def SurrogateDiagonalTailChunk000Sub000Block030Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1293
    = surrogateDiagTailX0RatChunk000Sub000Block030Part005

theorem surrogateDiagonalTailChunk000Sub000Block030Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part005] using hcert

def TailChunk000Sub000Block030Part006SupportExplicit : Finset ℕ :=
  ([1294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part006 : ℚ :=
  (52252868425 : ℚ) / 108867171490482

def SurrogateDiagonalTailChunk000Sub000Block030Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1294
    = surrogateDiagTailX0RatChunk000Sub000Block030Part006

theorem surrogateDiagonalTailChunk000Sub000Block030Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part006] using hcert

def TailChunk000Sub000Block030Part007SupportExplicit : Finset ℕ :=
  ([1295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part007 : ℚ :=
  (116272160375 : ℚ) / 696709661589504

def SurrogateDiagonalTailChunk000Sub000Block030Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1295
    = surrogateDiagTailX0RatChunk000Sub000Block030Part007

theorem surrogateDiagonalTailChunk000Sub000Block030Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part007] using hcert

def TailChunk000Sub000Block030Part008SupportExplicit : Finset ℕ :=
  ([1297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part008 : ℚ :=
  (210149959325 : ℚ) / 3527092661796864

def SurrogateDiagonalTailChunk000Sub000Block030Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1297
    = surrogateDiagTailX0RatChunk000Sub000Block030Part008

theorem surrogateDiagonalTailChunk000Sub000Block030Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part008] using hcert

def TailChunk000Sub000Block030Part009SupportExplicit : Finset ℕ :=
  ([1298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part009 : ℚ :=
  (3749988617 : ℚ) / 5659379649600

def SurrogateDiagonalTailChunk000Sub000Block030Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1298
    = surrogateDiagTailX0RatChunk000Sub000Block030Part009

theorem surrogateDiagonalTailChunk000Sub000Block030Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part009] using hcert

def TailChunk000Sub000Block030Part010SupportExplicit : Finset ℕ :=
  ([1299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part010 : ℚ :=
  (18703975 : ℚ) / 92876046336

def SurrogateDiagonalTailChunk000Sub000Block030Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1299
    = surrogateDiagTailX0RatChunk000Sub000Block030Part010

theorem surrogateDiagonalTailChunk000Sub000Block030Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part010] using hcert

def TailChunk000Sub000Block030Part011SupportExplicit : Finset ℕ :=
  ([1301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part011 : ℚ :=
  (8457927197 : ℚ) / 142833561000000

def SurrogateDiagonalTailChunk000Sub000Block030Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1301
    = surrogateDiagTailX0RatChunk000Sub000Block030Part011

theorem surrogateDiagonalTailChunk000Sub000Block030Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part011] using hcert

def TailChunk000Sub000Block030Part012SupportExplicit : Finset ℕ :=
  ([1302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part012 : ℚ :=
  (160659511 : ℚ) / 62220441600

def SurrogateDiagonalTailChunk000Sub000Block030Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1302
    = surrogateDiagTailX0RatChunk000Sub000Block030Part012

theorem surrogateDiagonalTailChunk000Sub000Block030Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part012] using hcert

def TailChunk000Sub000Block030Part013SupportExplicit : Finset ℕ :=
  ([1303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part013 : ℚ :=
  (212098789325 : ℚ) / 3592864181170404

def SurrogateDiagonalTailChunk000Sub000Block030Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1303
    = surrogateDiagTailX0RatChunk000Sub000Block030Part013

theorem surrogateDiagonalTailChunk000Sub000Block030Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part013] using hcert

def TailChunk000Sub000Block030Part014SupportExplicit : Finset ℕ :=
  ([1306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part014 : ℚ :=
  (53226503425 : ℚ) / 112968470936352

def SurrogateDiagonalTailChunk000Sub000Block030Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1306
    = surrogateDiagTailX0RatChunk000Sub000Block030Part014

theorem surrogateDiagonalTailChunk000Sub000Block030Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part014] using hcert

def TailChunk000Sub000Block030Part015SupportExplicit : Finset ℕ :=
  ([1307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part015 : ℚ :=
  (213403006325 : ℚ) / 3637220004161124

def SurrogateDiagonalTailChunk000Sub000Block030Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1307
    = surrogateDiagTailX0RatChunk000Sub000Block030Part015

theorem surrogateDiagonalTailChunk000Sub000Block030Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part015] using hcert

def TailChunk000Sub000Block030Part016SupportExplicit : Finset ℕ :=
  ([1309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part016 : ℚ :=
  (1241745607 : ℚ) / 8495164293120

def SurrogateDiagonalTailChunk000Sub000Block030Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1309
    = surrogateDiagTailX0RatChunk000Sub000Block030Part016

theorem surrogateDiagonalTailChunk000Sub000Block030Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part016] using hcert

def TailChunk000Sub000Block030Part017SupportExplicit : Finset ℕ :=
  ([1310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part017 : ℚ :=
  (3046285991 : ℚ) / 3656539161600

def SurrogateDiagonalTailChunk000Sub000Block030Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1310
    = surrogateDiagTailX0RatChunk000Sub000Block030Part017

theorem surrogateDiagonalTailChunk000Sub000Block030Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part017] using hcert

def TailChunk000Sub000Block030Part018SupportExplicit : Finset ℕ :=
  ([1311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part018 : ℚ :=
  (20720445925 : ℚ) / 81987253691904

def SurrogateDiagonalTailChunk000Sub000Block030Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1311
    = surrogateDiagTailX0RatChunk000Sub000Block030Part018

theorem surrogateDiagonalTailChunk000Sub000Block030Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part018] using hcert

def TailChunk000Sub000Block030Part019SupportExplicit : Finset ℕ :=
  ([1313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part019 : ℚ :=
  (1046780341 : ℚ) / 13826764800000

def SurrogateDiagonalTailChunk000Sub000Block030Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1313
    = surrogateDiagTailX0RatChunk000Sub000Block030Part019

theorem surrogateDiagonalTailChunk000Sub000Block030Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part019] using hcert

def TailChunk000Sub000Block030Part020SupportExplicit : Finset ℕ :=
  ([1315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part020 : ℚ :=
  (170121504575 : ℚ) / 1508141163439104

def SurrogateDiagonalTailChunk000Sub000Block030Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1315
    = surrogateDiagTailX0RatChunk000Sub000Block030Part020

theorem surrogateDiagonalTailChunk000Sub000Block030Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part020] using hcert

def TailChunk000Sub000Block030Part021SupportExplicit : Finset ℕ :=
  ([1317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part021 : ℚ :=
  (19225975 : ℚ) / 98144320896

def SurrogateDiagonalTailChunk000Sub000Block030Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1317
    = surrogateDiagTailX0RatChunk000Sub000Block030Part021

theorem surrogateDiagonalTailChunk000Sub000Block030Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part021] using hcert

def TailChunk000Sub000Block030Part022SupportExplicit : Finset ℕ :=
  ([1318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part022 : ℚ :=
  (54209125825 : ℚ) / 117184573038162

def SurrogateDiagonalTailChunk000Sub000Block030Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1318
    = surrogateDiagTailX0RatChunk000Sub000Block030Part022

theorem surrogateDiagonalTailChunk000Sub000Block030Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part022] using hcert

def TailChunk000Sub000Block030Part023SupportExplicit : Finset ℕ :=
  ([1319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part023 : ℚ :=
  (108691568475 : ℚ) / 2515169426111896

def SurrogateDiagonalTailChunk000Sub000Block030Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1319
    = surrogateDiagTailX0RatChunk000Sub000Block030Part023

theorem surrogateDiagonalTailChunk000Sub000Block030Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part023] using hcert

def TailChunk000Sub000Block030Part024SupportExplicit : Finset ℕ :=
  ([1321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block030Part024 : ℚ :=
  (8719969877 : ℚ) / 151828247577600

def SurrogateDiagonalTailChunk000Sub000Block030Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1321
    = surrogateDiagTailX0RatChunk000Sub000Block030Part024

theorem surrogateDiagonalTailChunk000Sub000Block030Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block030Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block030Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block030Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block030Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block030Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block030HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block030Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block030Part000
    + surrogateDiagTailX0RatChunk000Sub000Block030Part001
    + surrogateDiagTailX0RatChunk000Sub000Block030Part002
    + surrogateDiagTailX0RatChunk000Sub000Block030Part003
    + surrogateDiagTailX0RatChunk000Sub000Block030Part004
    + surrogateDiagTailX0RatChunk000Sub000Block030Part005
    + surrogateDiagTailX0RatChunk000Sub000Block030Part006
    + surrogateDiagTailX0RatChunk000Sub000Block030Part007
    + surrogateDiagTailX0RatChunk000Sub000Block030Part008
    + surrogateDiagTailX0RatChunk000Sub000Block030Part009

def surrogateDiagonalTailChunk000Sub000Block030MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block030Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block030Part010
    + surrogateDiagTailX0RatChunk000Sub000Block030Part011
    + surrogateDiagTailX0RatChunk000Sub000Block030Part012
    + surrogateDiagTailX0RatChunk000Sub000Block030Part013
    + surrogateDiagTailX0RatChunk000Sub000Block030Part014
    + surrogateDiagTailX0RatChunk000Sub000Block030Part015
    + surrogateDiagTailX0RatChunk000Sub000Block030Part016
    + surrogateDiagTailX0RatChunk000Sub000Block030Part017
    + surrogateDiagTailX0RatChunk000Sub000Block030Part018
    + surrogateDiagTailX0RatChunk000Sub000Block030Part019

def surrogateDiagonalTailChunk000Sub000Block030TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block030Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block030Part020
    + surrogateDiagTailX0RatChunk000Sub000Block030Part021
    + surrogateDiagTailX0RatChunk000Sub000Block030Part022
    + surrogateDiagTailX0RatChunk000Sub000Block030Part023
    + surrogateDiagTailX0RatChunk000Sub000Block030Part024

def surrogateDiagonalTailChunk000Sub000Block030Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block030HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block030MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block030TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block030 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block030Part000
    + surrogateDiagTailX0RatChunk000Sub000Block030Part001
    + surrogateDiagTailX0RatChunk000Sub000Block030Part002
    + surrogateDiagTailX0RatChunk000Sub000Block030Part003
    + surrogateDiagTailX0RatChunk000Sub000Block030Part004
    + surrogateDiagTailX0RatChunk000Sub000Block030Part005
    + surrogateDiagTailX0RatChunk000Sub000Block030Part006
    + surrogateDiagTailX0RatChunk000Sub000Block030Part007
    + surrogateDiagTailX0RatChunk000Sub000Block030Part008
    + surrogateDiagTailX0RatChunk000Sub000Block030Part009
    + surrogateDiagTailX0RatChunk000Sub000Block030Part010
    + surrogateDiagTailX0RatChunk000Sub000Block030Part011
    + surrogateDiagTailX0RatChunk000Sub000Block030Part012
    + surrogateDiagTailX0RatChunk000Sub000Block030Part013
    + surrogateDiagTailX0RatChunk000Sub000Block030Part014
    + surrogateDiagTailX0RatChunk000Sub000Block030Part015
    + surrogateDiagTailX0RatChunk000Sub000Block030Part016
    + surrogateDiagTailX0RatChunk000Sub000Block030Part017
    + surrogateDiagTailX0RatChunk000Sub000Block030Part018
    + surrogateDiagTailX0RatChunk000Sub000Block030Part019
    + surrogateDiagTailX0RatChunk000Sub000Block030Part020
    + surrogateDiagTailX0RatChunk000Sub000Block030Part021
    + surrogateDiagTailX0RatChunk000Sub000Block030Part022
    + surrogateDiagTailX0RatChunk000Sub000Block030Part023
    + surrogateDiagTailX0RatChunk000Sub000Block030Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block030_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block030Head + surrogateDiagTailX0RatChunk000Sub000Block030Mid + surrogateDiagTailX0RatChunk000Sub000Block030Tail =
      surrogateDiagTailX0RatChunk000Sub000Block030 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block030Head surrogateDiagTailX0RatChunk000Sub000Block030Mid surrogateDiagTailX0RatChunk000Sub000Block030Tail surrogateDiagTailX0RatChunk000Sub000Block030
  ring

def SurrogateDiagonalTailChunk000Sub000Block030HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block030HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block030Head

def SurrogateDiagonalTailChunk000Sub000Block030MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block030MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block030Mid

def SurrogateDiagonalTailChunk000Sub000Block030TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block030TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block030Tail

theorem surrogateDiagonalTailChunk000Sub000Block030_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block030HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block030MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block030TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block030Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block030 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block030HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block030MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block030TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block030Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block030_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

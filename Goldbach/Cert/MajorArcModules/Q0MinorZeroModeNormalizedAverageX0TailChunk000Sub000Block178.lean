import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [178,179). -/

/-- Block 178 covers tail-support indices [4450,4475) and q from 7370 to 7413. -/

def TailChunk000Sub000Block178Part000SupportExplicit : Finset ℕ :=
  ([7370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part000 : ℚ :=
  (21826964459 : ℚ) / 2429251961241600

def SurrogateDiagonalTailChunk000Sub000Block178Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7370
    = surrogateDiagTailX0RatChunk000Sub000Block178Part000

theorem surrogateDiagonalTailChunk000Sub000Block178Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part000] using hcert

def TailChunk000Sub000Block178Part001SupportExplicit : Finset ℕ :=
  ([7373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part001 : ℚ :=
  (65864543153 : ℚ) / 134396153856000000

def SurrogateDiagonalTailChunk000Sub000Block178Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7373
    = surrogateDiagTailX0RatChunk000Sub000Block178Part001

theorem surrogateDiagonalTailChunk000Sub000Block178Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part001] using hcert

def TailChunk000Sub000Block178Part002SupportExplicit : Finset ℕ :=
  ([7374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part002 : ℚ :=
  (660480880525 : ℚ) / 90978821896194048

def SurrogateDiagonalTailChunk000Sub000Block178Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7374
    = surrogateDiagTailX0RatChunk000Sub000Block178Part002

theorem surrogateDiagonalTailChunk000Sub000Block178Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part002] using hcert

def TailChunk000Sub000Block178Part003SupportExplicit : Finset ℕ :=
  ([7377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part003 : ℚ :=
  (236122276775 : ℚ) / 182551064070711696

def SurrogateDiagonalTailChunk000Sub000Block178Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7377
    = surrogateDiagTailX0RatChunk000Sub000Block178Part003

theorem surrogateDiagonalTailChunk000Sub000Block178Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part003] using hcert

def TailChunk000Sub000Block178Part004SupportExplicit : Finset ℕ :=
  ([7378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part004 : ℚ :=
  (360064847 : ℚ) / 84951642931200

def SurrogateDiagonalTailChunk000Sub000Block178Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7378
    = surrogateDiagTailX0RatChunk000Sub000Block178Part004

theorem surrogateDiagonalTailChunk000Sub000Block178Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part004] using hcert

def TailChunk000Sub000Block178Part005SupportExplicit : Finset ℕ :=
  ([7379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part005 : ℚ :=
  (410045344625 : ℚ) / 828832156172257536

def SurrogateDiagonalTailChunk000Sub000Block178Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7379
    = surrogateDiagTailX0RatChunk000Sub000Block178Part005

theorem surrogateDiagonalTailChunk000Sub000Block178Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part005] using hcert

def TailChunk000Sub000Block178Part006SupportExplicit : Finset ℕ :=
  ([7382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part006 : ℚ :=
  (340587025 : ℚ) / 185435258845842

def SurrogateDiagonalTailChunk000Sub000Block178Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7382
    = surrogateDiagTailX0RatChunk000Sub000Block178Part006

theorem surrogateDiagonalTailChunk000Sub000Block178Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part006] using hcert

def TailChunk000Sub000Block178Part007SupportExplicit : Finset ℕ :=
  ([7383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part007 : ℚ :=
  (1776471548275 : ℚ) / 1183207805209233408

def SurrogateDiagonalTailChunk000Sub000Block178Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7383
    = surrogateDiagTailX0RatChunk000Sub000Block178Part007

theorem surrogateDiagonalTailChunk000Sub000Block178Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part007] using hcert

def TailChunk000Sub000Block178Part008SupportExplicit : Finset ℕ :=
  ([7385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part008 : ℚ :=
  (40341505163 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub000Block178Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7385
    = surrogateDiagTailX0RatChunk000Sub000Block178Part008

theorem surrogateDiagonalTailChunk000Sub000Block178Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part008] using hcert

def TailChunk000Sub000Block178Part009SupportExplicit : Finset ℕ :=
  ([7386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part009 : ℚ :=
  (26505279967 : ℚ) / 3662918693251200

def SurrogateDiagonalTailChunk000Sub000Block178Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7386
    = surrogateDiagTailX0RatChunk000Sub000Block178Part009

theorem surrogateDiagonalTailChunk000Sub000Block178Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part009] using hcert

def TailChunk000Sub000Block178Part010SupportExplicit : Finset ℕ :=
  ([7387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part010 : ℚ :=
  (826803308425 : ℚ) / 1694934679320993792

def SurrogateDiagonalTailChunk000Sub000Block178Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7387
    = surrogateDiagTailX0RatChunk000Sub000Block178Part010

theorem surrogateDiagonalTailChunk000Sub000Block178Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part010] using hcert

def TailChunk000Sub000Block178Part011SupportExplicit : Finset ℕ :=
  ([7390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part011 : ℚ :=
  (250085899325 : ℚ) / 63295235019380736

def SurrogateDiagonalTailChunk000Sub000Block178Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7390
    = surrogateDiagTailX0RatChunk000Sub000Block178Part011

theorem surrogateDiagonalTailChunk000Sub000Block178Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part011] using hcert

def TailChunk000Sub000Block178Part012SupportExplicit : Finset ℕ :=
  ([7391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part012 : ℚ :=
  (3167589951925 : ℚ) / 5948997435018528768

def SurrogateDiagonalTailChunk000Sub000Block178Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7391
    = surrogateDiagTailX0RatChunk000Sub000Block178Part012

theorem surrogateDiagonalTailChunk000Sub000Block178Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part012] using hcert

def TailChunk000Sub000Block178Part013SupportExplicit : Finset ℕ :=
  ([7393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part013 : ℚ :=
  (854007015625 : ℚ) / 1866442866861146112

def SurrogateDiagonalTailChunk000Sub000Block178Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7393
    = surrogateDiagTailX0RatChunk000Sub000Block178Part013

theorem surrogateDiagonalTailChunk000Sub000Block178Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part013] using hcert

def TailChunk000Sub000Block178Part014SupportExplicit : Finset ℕ :=
  ([7394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part014 : ℚ :=
  (213559515625 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub000Block178Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7394
    = surrogateDiagTailX0RatChunk000Sub000Block178Part014

theorem surrogateDiagonalTailChunk000Sub000Block178Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part014] using hcert

def TailChunk000Sub000Block178Part015SupportExplicit : Finset ℕ :=
  ([7395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part015 : ℚ :=
  (426488123625 : ℚ) / 137523718946553856

def SurrogateDiagonalTailChunk000Sub000Block178Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7395
    = surrogateDiagTailX0RatChunk000Sub000Block178Part015

theorem surrogateDiagonalTailChunk000Sub000Block178Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part015] using hcert

def TailChunk000Sub000Block178Part016SupportExplicit : Finset ℕ :=
  ([7397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part016 : ℚ :=
  (5994572675 : ℚ) / 10540840090788864

def SurrogateDiagonalTailChunk000Sub000Block178Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7397
    = surrogateDiagTailX0RatChunk000Sub000Block178Part016

theorem surrogateDiagonalTailChunk000Sub000Block178Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part016] using hcert

def TailChunk000Sub000Block178Part017SupportExplicit : Finset ℕ :=
  ([7401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part017 : ℚ :=
  (118830636475 : ℚ) / 92469635969988168

def SurrogateDiagonalTailChunk000Sub000Block178Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7401
    = surrogateDiagTailX0RatChunk000Sub000Block178Part017

theorem surrogateDiagonalTailChunk000Sub000Block178Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part017] using hcert

def TailChunk000Sub000Block178Part018SupportExplicit : Finset ℕ :=
  ([7402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part018 : ℚ :=
  (13697401 : ℚ) / 7498143328800

def SurrogateDiagonalTailChunk000Sub000Block178Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7402
    = surrogateDiagTailX0RatChunk000Sub000Block178Part018

theorem surrogateDiagonalTailChunk000Sub000Block178Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part018] using hcert

def TailChunk000Sub000Block178Part019SupportExplicit : Finset ℕ :=
  ([7403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part019 : ℚ :=
  (120945722101 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub000Block178Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7403
    = surrogateDiagTailX0RatChunk000Sub000Block178Part019

theorem surrogateDiagonalTailChunk000Sub000Block178Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part019] using hcert

def TailChunk000Sub000Block178Part020SupportExplicit : Finset ℕ :=
  ([7405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part020 : ℚ :=
  (32877781239 : ℚ) / 40949860099686400

def SurrogateDiagonalTailChunk000Sub000Block178Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7405
    = surrogateDiagTailX0RatChunk000Sub000Block178Part020

theorem surrogateDiagonalTailChunk000Sub000Block178Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part020] using hcert

def TailChunk000Sub000Block178Part021SupportExplicit : Finset ℕ :=
  ([7409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part021 : ℚ :=
  (32633565667 : ℚ) / 64985985002080800

def SurrogateDiagonalTailChunk000Sub000Block178Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7409
    = surrogateDiagTailX0RatChunk000Sub000Block178Part021

theorem surrogateDiagonalTailChunk000Sub000Block178Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part021] using hcert

def TailChunk000Sub000Block178Part022SupportExplicit : Finset ℕ :=
  ([7410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part022 : ℚ :=
  (311505088925 : ℚ) / 11147354585432064

def SurrogateDiagonalTailChunk000Sub000Block178Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7410
    = surrogateDiagTailX0RatChunk000Sub000Block178Part022

theorem surrogateDiagonalTailChunk000Sub000Block178Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part022] using hcert

def TailChunk000Sub000Block178Part023SupportExplicit : Finset ℕ :=
  ([7411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part023 : ℚ :=
  (1373073025 : ℚ) / 3015502425499122

def SurrogateDiagonalTailChunk000Sub000Block178Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7411
    = surrogateDiagTailX0RatChunk000Sub000Block178Part023

theorem surrogateDiagonalTailChunk000Sub000Block178Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part023] using hcert

def TailChunk000Sub000Block178Part024SupportExplicit : Finset ℕ :=
  ([7413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block178Part024 : ℚ :=
  (86692566775 : ℚ) / 44223182369980416

def SurrogateDiagonalTailChunk000Sub000Block178Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7413
    = surrogateDiagTailX0RatChunk000Sub000Block178Part024

theorem surrogateDiagonalTailChunk000Sub000Block178Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block178Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block178Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block178Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block178Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block178Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block178HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block178Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part000
    + surrogateDiagTailX0RatChunk000Sub000Block178Part001
    + surrogateDiagTailX0RatChunk000Sub000Block178Part002
    + surrogateDiagTailX0RatChunk000Sub000Block178Part003
    + surrogateDiagTailX0RatChunk000Sub000Block178Part004
    + surrogateDiagTailX0RatChunk000Sub000Block178Part005
    + surrogateDiagTailX0RatChunk000Sub000Block178Part006
    + surrogateDiagTailX0RatChunk000Sub000Block178Part007
    + surrogateDiagTailX0RatChunk000Sub000Block178Part008
    + surrogateDiagTailX0RatChunk000Sub000Block178Part009

def surrogateDiagonalTailChunk000Sub000Block178MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block178Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part010
    + surrogateDiagTailX0RatChunk000Sub000Block178Part011
    + surrogateDiagTailX0RatChunk000Sub000Block178Part012
    + surrogateDiagTailX0RatChunk000Sub000Block178Part013
    + surrogateDiagTailX0RatChunk000Sub000Block178Part014
    + surrogateDiagTailX0RatChunk000Sub000Block178Part015
    + surrogateDiagTailX0RatChunk000Sub000Block178Part016
    + surrogateDiagTailX0RatChunk000Sub000Block178Part017
    + surrogateDiagTailX0RatChunk000Sub000Block178Part018
    + surrogateDiagTailX0RatChunk000Sub000Block178Part019

def surrogateDiagonalTailChunk000Sub000Block178TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block178Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part020
    + surrogateDiagTailX0RatChunk000Sub000Block178Part021
    + surrogateDiagTailX0RatChunk000Sub000Block178Part022
    + surrogateDiagTailX0RatChunk000Sub000Block178Part023
    + surrogateDiagTailX0RatChunk000Sub000Block178Part024

def surrogateDiagonalTailChunk000Sub000Block178Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block178HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block178MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block178TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block178 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block178Part000
    + surrogateDiagTailX0RatChunk000Sub000Block178Part001
    + surrogateDiagTailX0RatChunk000Sub000Block178Part002
    + surrogateDiagTailX0RatChunk000Sub000Block178Part003
    + surrogateDiagTailX0RatChunk000Sub000Block178Part004
    + surrogateDiagTailX0RatChunk000Sub000Block178Part005
    + surrogateDiagTailX0RatChunk000Sub000Block178Part006
    + surrogateDiagTailX0RatChunk000Sub000Block178Part007
    + surrogateDiagTailX0RatChunk000Sub000Block178Part008
    + surrogateDiagTailX0RatChunk000Sub000Block178Part009
    + surrogateDiagTailX0RatChunk000Sub000Block178Part010
    + surrogateDiagTailX0RatChunk000Sub000Block178Part011
    + surrogateDiagTailX0RatChunk000Sub000Block178Part012
    + surrogateDiagTailX0RatChunk000Sub000Block178Part013
    + surrogateDiagTailX0RatChunk000Sub000Block178Part014
    + surrogateDiagTailX0RatChunk000Sub000Block178Part015
    + surrogateDiagTailX0RatChunk000Sub000Block178Part016
    + surrogateDiagTailX0RatChunk000Sub000Block178Part017
    + surrogateDiagTailX0RatChunk000Sub000Block178Part018
    + surrogateDiagTailX0RatChunk000Sub000Block178Part019
    + surrogateDiagTailX0RatChunk000Sub000Block178Part020
    + surrogateDiagTailX0RatChunk000Sub000Block178Part021
    + surrogateDiagTailX0RatChunk000Sub000Block178Part022
    + surrogateDiagTailX0RatChunk000Sub000Block178Part023
    + surrogateDiagTailX0RatChunk000Sub000Block178Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block178_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block178Head + surrogateDiagTailX0RatChunk000Sub000Block178Mid + surrogateDiagTailX0RatChunk000Sub000Block178Tail =
      surrogateDiagTailX0RatChunk000Sub000Block178 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block178Head surrogateDiagTailX0RatChunk000Sub000Block178Mid surrogateDiagTailX0RatChunk000Sub000Block178Tail surrogateDiagTailX0RatChunk000Sub000Block178
  ring

def SurrogateDiagonalTailChunk000Sub000Block178HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block178HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block178Head

def SurrogateDiagonalTailChunk000Sub000Block178MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block178MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block178Mid

def SurrogateDiagonalTailChunk000Sub000Block178TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block178TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block178Tail

theorem surrogateDiagonalTailChunk000Sub000Block178_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block178HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block178MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block178TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block178Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block178 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block178HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block178MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block178TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block178Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block178_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

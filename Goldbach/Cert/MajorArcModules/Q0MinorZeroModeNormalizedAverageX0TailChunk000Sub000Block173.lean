import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [173,174). -/

/-- Block 173 covers tail-support indices [4325,4350) and q from 7169 to 7207. -/

def TailChunk000Sub000Block173Part000SupportExplicit : Finset ℕ :=
  ([7169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part000 : ℚ :=
  (389040297875 : ℚ) / 748748689233968016

def SurrogateDiagonalTailChunk000Sub000Block173Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7169
    = surrogateDiagTailX0RatChunk000Sub000Block173Part000

theorem surrogateDiagonalTailChunk000Sub000Block173Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part000] using hcert

def TailChunk000Sub000Block173Part001SupportExplicit : Finset ℕ :=
  ([7170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part001 : ℚ :=
  (129861506575 : ℚ) / 8215512178040832

def SurrogateDiagonalTailChunk000Sub000Block173Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7170
    = surrogateDiagTailX0RatChunk000Sub000Block173Part001

theorem surrogateDiagonalTailChunk000Sub000Block173Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part001] using hcert

def TailChunk000Sub000Block173Part002SupportExplicit : Finset ℕ :=
  ([7171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part002 : ℚ :=
  (17800722277 : ℚ) / 34306860000000000

def SurrogateDiagonalTailChunk000Sub000Block173Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7171
    = surrogateDiagTailX0RatChunk000Sub000Block173Part002

theorem surrogateDiagonalTailChunk000Sub000Block173Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part002] using hcert

def TailChunk000Sub000Block173Part003SupportExplicit : Finset ℕ :=
  ([7174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part003 : ℚ :=
  (15482042729 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub000Block173Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7174
    = surrogateDiagTailX0RatChunk000Sub000Block173Part003

theorem surrogateDiagonalTailChunk000Sub000Block173Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part003] using hcert

def TailChunk000Sub000Block173Part004SupportExplicit : Finset ℕ :=
  ([7177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part004 : ℚ :=
  (804833265625 : ℚ) / 1657664312344515072

def SurrogateDiagonalTailChunk000Sub000Block173Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7177
    = surrogateDiagTailX0RatChunk000Sub000Block173Part004

theorem surrogateDiagonalTailChunk000Sub000Block173Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part004] using hcert

def TailChunk000Sub000Block173Part005SupportExplicit : Finset ℕ :=
  ([7178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part005 : ℚ :=
  (29154003625 : ℚ) / 13211679508660224

def SurrogateDiagonalTailChunk000Sub000Block173Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7178
    = surrogateDiagTailX0RatChunk000Sub000Block173Part005

theorem surrogateDiagonalTailChunk000Sub000Block173Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part005] using hcert

def TailChunk000Sub000Block173Part006SupportExplicit : Finset ℕ :=
  ([7179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part006 : ℚ :=
  (214624875 : ℚ) / 130949755715584

def SurrogateDiagonalTailChunk000Sub000Block173Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7179
    = surrogateDiagTailX0RatChunk000Sub000Block173Part006

theorem surrogateDiagonalTailChunk000Sub000Block173Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part006] using hcert

def TailChunk000Sub000Block173Part007SupportExplicit : Finset ℕ :=
  ([7181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part007 : ℚ :=
  (774979446775 : ℚ) / 1477054027959404832

def SurrogateDiagonalTailChunk000Sub000Block173Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7181
    = surrogateDiagTailX0RatChunk000Sub000Block173Part007

theorem surrogateDiagonalTailChunk000Sub000Block173Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part007] using hcert

def TailChunk000Sub000Block173Part008SupportExplicit : Finset ℕ :=
  ([7183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part008 : ℚ :=
  (113861024521 : ℚ) / 180749553498163200

def SurrogateDiagonalTailChunk000Sub000Block173Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7183
    = surrogateDiagTailX0RatChunk000Sub000Block173Part008

theorem surrogateDiagonalTailChunk000Sub000Block173Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part008] using hcert

def TailChunk000Sub000Block173Part009SupportExplicit : Finset ℕ :=
  ([7185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part009 : ℚ :=
  (233698753875 : ℚ) / 89114247242498048

def SurrogateDiagonalTailChunk000Sub000Block173Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7185
    = surrogateDiagTailX0RatChunk000Sub000Block173Part009

theorem surrogateDiagonalTailChunk000Sub000Block173Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part009] using hcert

def TailChunk000Sub000Block173Part010SupportExplicit : Finset ℕ :=
  ([7186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part010 : ℚ :=
  (201713265625 : ℚ) / 104066794991718912

def SurrogateDiagonalTailChunk000Sub000Block173Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7186
    = surrogateDiagTailX0RatChunk000Sub000Block173Part010

theorem surrogateDiagonalTailChunk000Sub000Block173Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part010] using hcert

def TailChunk000Sub000Block173Part011SupportExplicit : Finset ℕ :=
  ([7187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part011 : ℚ :=
  (807077640625 : ℚ) / 1666923691106616402

def SurrogateDiagonalTailChunk000Sub000Block173Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7187
    = surrogateDiagTailX0RatChunk000Sub000Block173Part011

theorem surrogateDiagonalTailChunk000Sub000Block173Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part011] using hcert

def TailChunk000Sub000Block173Part012SupportExplicit : Finset ℕ :=
  ([7189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part012 : ℚ :=
  (2341319035675 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub000Block173Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7189
    = surrogateDiagTailX0RatChunk000Sub000Block173Part012

theorem surrogateDiagonalTailChunk000Sub000Block173Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part012] using hcert

def TailChunk000Sub000Block173Part013SupportExplicit : Finset ℕ :=
  ([7190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part013 : ℚ :=
  (710211151975 : ℚ) / 170123614447945728

def SurrogateDiagonalTailChunk000Sub000Block173Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7190
    = surrogateDiagTailX0RatChunk000Sub000Block173Part013

theorem surrogateDiagonalTailChunk000Sub000Block173Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part013] using hcert

def TailChunk000Sub000Block173Part014SupportExplicit : Finset ℕ :=
  ([7193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part014 : ℚ :=
  (808425765625 : ℚ) / 1672497905081037312

def SurrogateDiagonalTailChunk000Sub000Block173Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7193
    = surrogateDiagTailX0RatChunk000Sub000Block173Part014

theorem surrogateDiagonalTailChunk000Sub000Block173Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part014] using hcert

def TailChunk000Sub000Block173Part015SupportExplicit : Finset ℕ :=
  ([7194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part015 : ℚ :=
  (7704657797 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub000Block173Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7194
    = surrogateDiagTailX0RatChunk000Sub000Block173Part015

theorem surrogateDiagonalTailChunk000Sub000Block173Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part015] using hcert

def TailChunk000Sub000Block173Part016SupportExplicit : Finset ℕ :=
  ([7195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part016 : ℚ :=
  (775978880475 : ℚ) / 912391254207502336

def SurrogateDiagonalTailChunk000Sub000Block173Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7195
    = surrogateDiagTailX0RatChunk000Sub000Block173Part016

theorem surrogateDiagonalTailChunk000Sub000Block173Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part016] using hcert

def TailChunk000Sub000Block173Part017SupportExplicit : Finset ℕ :=
  ([7197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part017 : ℚ :=
  (449478411925 : ℚ) / 330737595924486432

def SurrogateDiagonalTailChunk000Sub000Block173Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7197
    = surrogateDiagTailX0RatChunk000Sub000Block173Part017

theorem surrogateDiagonalTailChunk000Sub000Block173Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part017] using hcert

def TailChunk000Sub000Block173Part018SupportExplicit : Finset ℕ :=
  ([7198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part018 : ℚ :=
  (30996067931 : ℚ) / 7334556025881600

def SurrogateDiagonalTailChunk000Sub000Block173Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7198
    = surrogateDiagTailX0RatChunk000Sub000Block173Part018

theorem surrogateDiagonalTailChunk000Sub000Block173Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part018] using hcert

def TailChunk000Sub000Block173Part019SupportExplicit : Finset ℕ :=
  ([7199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part019 : ℚ :=
  (58524924175 : ℚ) / 106741331176955904

def SurrogateDiagonalTailChunk000Sub000Block173Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7199
    = surrogateDiagTailX0RatChunk000Sub000Block173Part019

theorem surrogateDiagonalTailChunk000Sub000Block173Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part019] using hcert

def TailChunk000Sub000Block173Part020SupportExplicit : Finset ℕ :=
  ([7201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part020 : ℚ :=
  (3006701241925 : ℚ) / 5359003968429030528

def SurrogateDiagonalTailChunk000Sub000Block173Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7201
    = surrogateDiagTailX0RatChunk000Sub000Block173Part020

theorem surrogateDiagonalTailChunk000Sub000Block173Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part020] using hcert

def TailChunk000Sub000Block173Part021SupportExplicit : Finset ℕ :=
  ([7202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part021 : ℚ :=
  (362826888475 : ℚ) / 75219108182433792

def SurrogateDiagonalTailChunk000Sub000Block173Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7202
    = surrogateDiagTailX0RatChunk000Sub000Block173Part021

theorem surrogateDiagonalTailChunk000Sub000Block173Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part021] using hcert

def TailChunk000Sub000Block173Part022SupportExplicit : Finset ℕ :=
  ([7205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part022 : ℚ :=
  (21506235691 : ℚ) / 18282695808000000

def SurrogateDiagonalTailChunk000Sub000Block173Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7205
    = surrogateDiagTailX0RatChunk000Sub000Block173Part022

theorem surrogateDiagonalTailChunk000Sub000Block173Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part022] using hcert

def TailChunk000Sub000Block173Part023SupportExplicit : Finset ℕ :=
  ([7206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part023 : ℚ :=
  (18014650097 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block173Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7206
    = surrogateDiagTailX0RatChunk000Sub000Block173Part023

theorem surrogateDiagonalTailChunk000Sub000Block173Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part023] using hcert

def TailChunk000Sub000Block173Part024SupportExplicit : Finset ℕ :=
  ([7207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block173Part024 : ℚ :=
  (811575765625 : ℚ) / 1685558766633267762

def SurrogateDiagonalTailChunk000Sub000Block173Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7207
    = surrogateDiagTailX0RatChunk000Sub000Block173Part024

theorem surrogateDiagonalTailChunk000Sub000Block173Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block173Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block173Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block173Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block173Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block173Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block173HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block173Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part000
    + surrogateDiagTailX0RatChunk000Sub000Block173Part001
    + surrogateDiagTailX0RatChunk000Sub000Block173Part002
    + surrogateDiagTailX0RatChunk000Sub000Block173Part003
    + surrogateDiagTailX0RatChunk000Sub000Block173Part004
    + surrogateDiagTailX0RatChunk000Sub000Block173Part005
    + surrogateDiagTailX0RatChunk000Sub000Block173Part006
    + surrogateDiagTailX0RatChunk000Sub000Block173Part007
    + surrogateDiagTailX0RatChunk000Sub000Block173Part008
    + surrogateDiagTailX0RatChunk000Sub000Block173Part009

def surrogateDiagonalTailChunk000Sub000Block173MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block173Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part010
    + surrogateDiagTailX0RatChunk000Sub000Block173Part011
    + surrogateDiagTailX0RatChunk000Sub000Block173Part012
    + surrogateDiagTailX0RatChunk000Sub000Block173Part013
    + surrogateDiagTailX0RatChunk000Sub000Block173Part014
    + surrogateDiagTailX0RatChunk000Sub000Block173Part015
    + surrogateDiagTailX0RatChunk000Sub000Block173Part016
    + surrogateDiagTailX0RatChunk000Sub000Block173Part017
    + surrogateDiagTailX0RatChunk000Sub000Block173Part018
    + surrogateDiagTailX0RatChunk000Sub000Block173Part019

def surrogateDiagonalTailChunk000Sub000Block173TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block173Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part020
    + surrogateDiagTailX0RatChunk000Sub000Block173Part021
    + surrogateDiagTailX0RatChunk000Sub000Block173Part022
    + surrogateDiagTailX0RatChunk000Sub000Block173Part023
    + surrogateDiagTailX0RatChunk000Sub000Block173Part024

def surrogateDiagonalTailChunk000Sub000Block173Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block173HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block173MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block173TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block173 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block173Part000
    + surrogateDiagTailX0RatChunk000Sub000Block173Part001
    + surrogateDiagTailX0RatChunk000Sub000Block173Part002
    + surrogateDiagTailX0RatChunk000Sub000Block173Part003
    + surrogateDiagTailX0RatChunk000Sub000Block173Part004
    + surrogateDiagTailX0RatChunk000Sub000Block173Part005
    + surrogateDiagTailX0RatChunk000Sub000Block173Part006
    + surrogateDiagTailX0RatChunk000Sub000Block173Part007
    + surrogateDiagTailX0RatChunk000Sub000Block173Part008
    + surrogateDiagTailX0RatChunk000Sub000Block173Part009
    + surrogateDiagTailX0RatChunk000Sub000Block173Part010
    + surrogateDiagTailX0RatChunk000Sub000Block173Part011
    + surrogateDiagTailX0RatChunk000Sub000Block173Part012
    + surrogateDiagTailX0RatChunk000Sub000Block173Part013
    + surrogateDiagTailX0RatChunk000Sub000Block173Part014
    + surrogateDiagTailX0RatChunk000Sub000Block173Part015
    + surrogateDiagTailX0RatChunk000Sub000Block173Part016
    + surrogateDiagTailX0RatChunk000Sub000Block173Part017
    + surrogateDiagTailX0RatChunk000Sub000Block173Part018
    + surrogateDiagTailX0RatChunk000Sub000Block173Part019
    + surrogateDiagTailX0RatChunk000Sub000Block173Part020
    + surrogateDiagTailX0RatChunk000Sub000Block173Part021
    + surrogateDiagTailX0RatChunk000Sub000Block173Part022
    + surrogateDiagTailX0RatChunk000Sub000Block173Part023
    + surrogateDiagTailX0RatChunk000Sub000Block173Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block173_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block173Head + surrogateDiagTailX0RatChunk000Sub000Block173Mid + surrogateDiagTailX0RatChunk000Sub000Block173Tail =
      surrogateDiagTailX0RatChunk000Sub000Block173 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block173Head surrogateDiagTailX0RatChunk000Sub000Block173Mid surrogateDiagTailX0RatChunk000Sub000Block173Tail surrogateDiagTailX0RatChunk000Sub000Block173
  ring

def SurrogateDiagonalTailChunk000Sub000Block173HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block173HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block173Head

def SurrogateDiagonalTailChunk000Sub000Block173MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block173MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block173Mid

def SurrogateDiagonalTailChunk000Sub000Block173TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block173TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block173Tail

theorem surrogateDiagonalTailChunk000Sub000Block173_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block173HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block173MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block173TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block173Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block173 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block173HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block173MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block173TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block173Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block173_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

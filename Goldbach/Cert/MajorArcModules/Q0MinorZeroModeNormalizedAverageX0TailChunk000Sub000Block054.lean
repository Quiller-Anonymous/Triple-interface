import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [54,55). -/

/- Block 054 covers tail-support indices [1350,1375) and q from 2271 to 2311. -/

def TailChunk000Sub000Block054Part000SupportExplicit : Finset ℕ :=
  ([2271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part000 : ℚ :=
  (232541574425 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block054Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2271
    = surrogateDiagTailX0RatChunk000Sub000Block054Part000

theorem surrogateDiagonalTailChunk000Sub000Block054Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part000] using hcert

def TailChunk000Sub000Block054Part001SupportExplicit : Finset ℕ :=
  ([2273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part001 : ℚ :=
  (322778899275 : ℚ) / 22209506693349376

def SurrogateDiagonalTailChunk000Sub000Block054Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2273
    = surrogateDiagTailX0RatChunk000Sub000Block054Part001

theorem surrogateDiagonalTailChunk000Sub000Block054Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part001] using hcert

def TailChunk000Sub000Block054Part002SupportExplicit : Finset ℕ :=
  ([2274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part002 : ℚ :=
  (35816189575 : ℚ) / 116685260705664

def SurrogateDiagonalTailChunk000Sub000Block054Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2274
    = surrogateDiagTailX0RatChunk000Sub000Block054Part002

theorem surrogateDiagonalTailChunk000Sub000Block054Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part002] using hcert

def TailChunk000Sub000Block054Part003SupportExplicit : Finset ℕ :=
  ([2278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part003 : ℚ :=
  (186260070575 : ℚ) / 1554721255194624

def SurrogateDiagonalTailChunk000Sub000Block054Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2278
    = surrogateDiagTailX0RatChunk000Sub000Block054Part003

theorem surrogateDiagonalTailChunk000Sub000Block054Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part003] using hcert

def TailChunk000Sub000Block054Part004SupportExplicit : Finset ℕ :=
  ([2279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part004 : ℚ :=
  (7716653825 : ℚ) / 702348042160128

def SurrogateDiagonalTailChunk000Sub000Block054Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2279
    = surrogateDiagTailX0RatChunk000Sub000Block054Part004

theorem surrogateDiagonalTailChunk000Sub000Block054Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part004] using hcert

def TailChunk000Sub000Block054Part005SupportExplicit : Finset ℕ :=
  ([2281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part005 : ℚ :=
  (26009602039 : ℚ) / 2702876723251200

def SurrogateDiagonalTailChunk000Sub000Block054Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2281
    = surrogateDiagTailX0RatChunk000Sub000Block054Part005

theorem surrogateDiagonalTailChunk000Sub000Block054Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part005] using hcert

def TailChunk000Sub000Block054Part006SupportExplicit : Finset ℕ :=
  ([2282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part006 : ℚ :=
  (15688889825 : ℚ) / 123999351391296

def SurrogateDiagonalTailChunk000Sub000Block054Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2282
    = surrogateDiagTailX0RatChunk000Sub000Block054Part006

theorem surrogateDiagonalTailChunk000Sub000Block054Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part006] using hcert

def TailChunk000Sub000Block054Part007SupportExplicit : Finset ℕ :=
  ([2283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part007 : ℚ :=
  (694119 : ℚ) / 21351792640

def SurrogateDiagonalTailChunk000Sub000Block054Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2283
    = surrogateDiagTailX0RatChunk000Sub000Block054Part007

theorem surrogateDiagonalTailChunk000Sub000Block054Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part007] using hcert

def TailChunk000Sub000Block054Part008SupportExplicit : Finset ℕ :=
  ([2285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part008 : ℚ :=
  (60760643125 : ℚ) / 2306454803841024

def SurrogateDiagonalTailChunk000Sub000Block054Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2285
    = surrogateDiagTailX0RatChunk000Sub000Block054Part008

theorem surrogateDiagonalTailChunk000Sub000Block054Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part008] using hcert

def TailChunk000Sub000Block054Part009SupportExplicit : Finset ℕ :=
  ([2287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part009 : ℚ :=
  (653665365775 : ℚ) / 68286014055956808

def SurrogateDiagonalTailChunk000Sub000Block054Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2287
    = surrogateDiagTailX0RatChunk000Sub000Block054Part009

theorem surrogateDiagonalTailChunk000Sub000Block054Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part009] using hcert

def TailChunk000Sub000Block054Part010SupportExplicit : Finset ℕ :=
  ([2289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part010 : ℚ :=
  (376311036175 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub000Block054Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2289
    = surrogateDiagTailX0RatChunk000Sub000Block054Part010

theorem surrogateDiagonalTailChunk000Sub000Block054Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part010] using hcert

def TailChunk000Sub000Block054Part011SupportExplicit : Finset ℕ :=
  ([2290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part011 : ℚ :=
  (316455385975 : ℚ) / 1729841102880768

def SurrogateDiagonalTailChunk000Sub000Block054Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2290
    = surrogateDiagTailX0RatChunk000Sub000Block054Part011

theorem surrogateDiagonalTailChunk000Sub000Block054Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part011] using hcert

def TailChunk000Sub000Block054Part012SupportExplicit : Finset ℕ :=
  ([2291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part012 : ℚ :=
  (78522379625 : ℚ) / 7111273926871296

def SurrogateDiagonalTailChunk000Sub000Block054Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2291
    = surrogateDiagTailX0RatChunk000Sub000Block054Part012

theorem surrogateDiagonalTailChunk000Sub000Block054Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part012] using hcert

def TailChunk000Sub000Block054Part013SupportExplicit : Finset ℕ :=
  ([2293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part013 : ℚ :=
  (657099678775 : ℚ) / 69005755025566848

def SurrogateDiagonalTailChunk000Sub000Block054Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2293
    = surrogateDiagTailX0RatChunk000Sub000Block054Part013

theorem surrogateDiagonalTailChunk000Sub000Block054Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part013] using hcert

def TailChunk000Sub000Block054Part014SupportExplicit : Finset ℕ :=
  ([2294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part014 : ℚ :=
  (341483701 : ℚ) / 3023913461760

def SurrogateDiagonalTailChunk000Sub000Block054Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2294
    = surrogateDiagTailX0RatChunk000Sub000Block054Part014

theorem surrogateDiagonalTailChunk000Sub000Block054Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part014] using hcert

def TailChunk000Sub000Block054Part015SupportExplicit : Finset ℕ :=
  ([2297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part015 : ℚ :=
  (659394219775 : ℚ) / 69488733096265728

def SurrogateDiagonalTailChunk000Sub000Block054Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2297
    = surrogateDiagTailX0RatChunk000Sub000Block054Part015

theorem surrogateDiagonalTailChunk000Sub000Block054Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part015] using hcert

def TailChunk000Sub000Block054Part016SupportExplicit : Finset ℕ :=
  ([2298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part016 : ℚ :=
  (114336852425 : ℚ) / 425961450775104

def SurrogateDiagonalTailChunk000Sub000Block054Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2298
    = surrogateDiagTailX0RatChunk000Sub000Block054Part016

theorem surrogateDiagonalTailChunk000Sub000Block054Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part016] using hcert

def TailChunk000Sub000Block054Part017SupportExplicit : Finset ℕ :=
  ([2301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part017 : ℚ :=
  (434466247975 : ℚ) / 9388231713128448

def SurrogateDiagonalTailChunk000Sub000Block054Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2301
    = surrogateDiagTailX0RatChunk000Sub000Block054Part017

theorem surrogateDiagonalTailChunk000Sub000Block054Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part017] using hcert

def TailChunk000Sub000Block054Part018SupportExplicit : Finset ℕ :=
  ([2302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part018 : ℚ :=
  (6620030597 : ℚ) / 87467802562500

def SurrogateDiagonalTailChunk000Sub000Block054Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2302
    = surrogateDiagTailX0RatChunk000Sub000Block054Part018

theorem surrogateDiagonalTailChunk000Sub000Block054Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part018] using hcert

def TailChunk000Sub000Block054Part019SupportExplicit : Finset ℕ :=
  ([2305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part019 : ℚ :=
  (1483907099 : ℚ) / 57322899087360

def SurrogateDiagonalTailChunk000Sub000Block054Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2305
    = surrogateDiagTailX0RatChunk000Sub000Block054Part019

theorem surrogateDiagonalTailChunk000Sub000Block054Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part019] using hcert

def TailChunk000Sub000Block054Part020SupportExplicit : Finset ℕ :=
  ([2306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part020 : ℚ :=
  (166076419325 : ℚ) / 2201946584776704

def SurrogateDiagonalTailChunk000Sub000Block054Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2306
    = surrogateDiagTailX0RatChunk000Sub000Block054Part020

theorem surrogateDiagonalTailChunk000Sub000Block054Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part020] using hcert

def TailChunk000Sub000Block054Part021SupportExplicit : Finset ℕ :=
  ([2307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part021 : ℚ :=
  (3281425 : ℚ) / 103079215104

def SurrogateDiagonalTailChunk000Sub000Block054Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2307
    = surrogateDiagTailX0RatChunk000Sub000Block054Part021

theorem surrogateDiagonalTailChunk000Sub000Block054Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part021] using hcert

def TailChunk000Sub000Block054Part022SupportExplicit : Finset ℕ :=
  ([2309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part022 : ℚ :=
  (666301837975 : ℚ) / 70952887926277248

def SurrogateDiagonalTailChunk000Sub000Block054Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2309
    = surrogateDiagTailX0RatChunk000Sub000Block054Part022

theorem surrogateDiagonalTailChunk000Sub000Block054Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part022] using hcert

def TailChunk000Sub000Block054Part023SupportExplicit : Finset ℕ :=
  ([2310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part023 : ℚ :=
  (9293503 : ℚ) / 7865892864

def SurrogateDiagonalTailChunk000Sub000Block054Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2310
    = surrogateDiagTailX0RatChunk000Sub000Block054Part023

theorem surrogateDiagonalTailChunk000Sub000Block054Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part023] using hcert

def TailChunk000Sub000Block054Part024SupportExplicit : Finset ℕ :=
  ([2311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block054Part024 : ℚ :=
  (26698264279 : ℚ) / 2847965800264200

def SurrogateDiagonalTailChunk000Sub000Block054Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2311
    = surrogateDiagTailX0RatChunk000Sub000Block054Part024

theorem surrogateDiagonalTailChunk000Sub000Block054Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block054Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block054Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block054Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block054Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block054Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block054HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block054Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block054Part000
    + surrogateDiagTailX0RatChunk000Sub000Block054Part001
    + surrogateDiagTailX0RatChunk000Sub000Block054Part002
    + surrogateDiagTailX0RatChunk000Sub000Block054Part003
    + surrogateDiagTailX0RatChunk000Sub000Block054Part004
    + surrogateDiagTailX0RatChunk000Sub000Block054Part005
    + surrogateDiagTailX0RatChunk000Sub000Block054Part006
    + surrogateDiagTailX0RatChunk000Sub000Block054Part007
    + surrogateDiagTailX0RatChunk000Sub000Block054Part008
    + surrogateDiagTailX0RatChunk000Sub000Block054Part009

def surrogateDiagonalTailChunk000Sub000Block054MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block054Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block054Part010
    + surrogateDiagTailX0RatChunk000Sub000Block054Part011
    + surrogateDiagTailX0RatChunk000Sub000Block054Part012
    + surrogateDiagTailX0RatChunk000Sub000Block054Part013
    + surrogateDiagTailX0RatChunk000Sub000Block054Part014
    + surrogateDiagTailX0RatChunk000Sub000Block054Part015
    + surrogateDiagTailX0RatChunk000Sub000Block054Part016
    + surrogateDiagTailX0RatChunk000Sub000Block054Part017
    + surrogateDiagTailX0RatChunk000Sub000Block054Part018
    + surrogateDiagTailX0RatChunk000Sub000Block054Part019

def surrogateDiagonalTailChunk000Sub000Block054TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block054Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block054Part020
    + surrogateDiagTailX0RatChunk000Sub000Block054Part021
    + surrogateDiagTailX0RatChunk000Sub000Block054Part022
    + surrogateDiagTailX0RatChunk000Sub000Block054Part023
    + surrogateDiagTailX0RatChunk000Sub000Block054Part024

def surrogateDiagonalTailChunk000Sub000Block054Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block054HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block054MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block054TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block054 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block054Part000
    + surrogateDiagTailX0RatChunk000Sub000Block054Part001
    + surrogateDiagTailX0RatChunk000Sub000Block054Part002
    + surrogateDiagTailX0RatChunk000Sub000Block054Part003
    + surrogateDiagTailX0RatChunk000Sub000Block054Part004
    + surrogateDiagTailX0RatChunk000Sub000Block054Part005
    + surrogateDiagTailX0RatChunk000Sub000Block054Part006
    + surrogateDiagTailX0RatChunk000Sub000Block054Part007
    + surrogateDiagTailX0RatChunk000Sub000Block054Part008
    + surrogateDiagTailX0RatChunk000Sub000Block054Part009
    + surrogateDiagTailX0RatChunk000Sub000Block054Part010
    + surrogateDiagTailX0RatChunk000Sub000Block054Part011
    + surrogateDiagTailX0RatChunk000Sub000Block054Part012
    + surrogateDiagTailX0RatChunk000Sub000Block054Part013
    + surrogateDiagTailX0RatChunk000Sub000Block054Part014
    + surrogateDiagTailX0RatChunk000Sub000Block054Part015
    + surrogateDiagTailX0RatChunk000Sub000Block054Part016
    + surrogateDiagTailX0RatChunk000Sub000Block054Part017
    + surrogateDiagTailX0RatChunk000Sub000Block054Part018
    + surrogateDiagTailX0RatChunk000Sub000Block054Part019
    + surrogateDiagTailX0RatChunk000Sub000Block054Part020
    + surrogateDiagTailX0RatChunk000Sub000Block054Part021
    + surrogateDiagTailX0RatChunk000Sub000Block054Part022
    + surrogateDiagTailX0RatChunk000Sub000Block054Part023
    + surrogateDiagTailX0RatChunk000Sub000Block054Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block054_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block054Head + surrogateDiagTailX0RatChunk000Sub000Block054Mid + surrogateDiagTailX0RatChunk000Sub000Block054Tail =
      surrogateDiagTailX0RatChunk000Sub000Block054 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block054Head surrogateDiagTailX0RatChunk000Sub000Block054Mid surrogateDiagTailX0RatChunk000Sub000Block054Tail surrogateDiagTailX0RatChunk000Sub000Block054
  ring

def SurrogateDiagonalTailChunk000Sub000Block054HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block054HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block054Head

def SurrogateDiagonalTailChunk000Sub000Block054MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block054MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block054Mid

def SurrogateDiagonalTailChunk000Sub000Block054TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block054TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block054Tail

theorem surrogateDiagonalTailChunk000Sub000Block054_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block054HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block054MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block054TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block054Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block054 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block054HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block054MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block054TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block054Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block054_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

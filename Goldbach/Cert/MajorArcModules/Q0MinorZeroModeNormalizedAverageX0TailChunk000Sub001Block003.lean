import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [3,4). -/

/-- Block 003 covers tail-support indices [5075,5100) and q from 8394 to 8437. -/

def TailChunk000Sub001Block003Part000SupportExplicit : Finset ℕ :=
  ([8394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part000 : ℚ :=
  (24450875 : ℚ) / 5092926660288

def SurrogateDiagonalTailChunk000Sub001Block003Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8394
    = surrogateDiagTailX0RatChunk000Sub001Block003Part000

theorem surrogateDiagonalTailChunk000Sub001Block003Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part000] using hcert

def TailChunk000Sub001Block003Part001SupportExplicit : Finset ℕ :=
  ([8395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part001 : ℚ :=
  (978185236975 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub001Block003Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8395
    = surrogateDiagTailX0RatChunk000Sub001Block003Part001

theorem surrogateDiagonalTailChunk000Sub001Block003Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part001] using hcert

def TailChunk000Sub001Block003Part002SupportExplicit : Finset ℕ :=
  ([8398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part002 : ℚ :=
  (157096911325 : ℚ) / 59452557788971008

def SurrogateDiagonalTailChunk000Sub001Block003Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8398
    = surrogateDiagTailX0RatChunk000Sub001Block003Part002

theorem surrogateDiagonalTailChunk000Sub001Block003Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part002] using hcert

def TailChunk000Sub001Block003Part003SupportExplicit : Finset ℕ :=
  ([8399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part003 : ℚ :=
  (3659763625 : ℚ) / 9510823877938704

def SurrogateDiagonalTailChunk000Sub001Block003Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8399
    = surrogateDiagTailX0RatChunk000Sub001Block003Part003

theorem surrogateDiagonalTailChunk000Sub001Block003Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part003] using hcert

def TailChunk000Sub001Block003Part004SupportExplicit : Finset ℕ :=
  ([8401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part004 : ℚ :=
  (167522565517 : ℚ) / 430553303442000000

def SurrogateDiagonalTailChunk000Sub001Block003Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8401
    = surrogateDiagTailX0RatChunk000Sub001Block003Part004

theorem surrogateDiagonalTailChunk000Sub001Block003Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part004] using hcert

def TailChunk000Sub001Block003Part005SupportExplicit : Finset ℕ :=
  ([8402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part005 : ℚ :=
  (17648401 : ℚ) / 12449273356800

def SurrogateDiagonalTailChunk000Sub001Block003Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8402
    = surrogateDiagTailX0RatChunk000Sub001Block003Part005

theorem surrogateDiagonalTailChunk000Sub001Block003Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part005] using hcert

def TailChunk000Sub001Block003Part006SupportExplicit : Finset ℕ :=
  ([8403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part006 : ℚ :=
  (49020337349 : ℚ) / 49182314496000000

def SurrogateDiagonalTailChunk000Sub001Block003Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8403
    = surrogateDiagTailX0RatChunk000Sub001Block003Part006

theorem surrogateDiagonalTailChunk000Sub001Block003Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part006] using hcert

def TailChunk000Sub001Block003Part007SupportExplicit : Finset ℕ :=
  ([8407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part007 : ℚ :=
  (7805359631 : ℚ) / 14932905984000000

def SurrogateDiagonalTailChunk000Sub001Block003Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8407
    = surrogateDiagTailX0RatChunk000Sub001Block003Part007

theorem surrogateDiagonalTailChunk000Sub001Block003Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part007] using hcert

def TailChunk000Sub001Block003Part008SupportExplicit : Finset ℕ :=
  ([8409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part008 : ℚ :=
  (76703708675 : ℚ) / 77067165663082404

def SurrogateDiagonalTailChunk000Sub001Block003Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8409
    = surrogateDiagTailX0RatChunk000Sub001Block003Part008

theorem surrogateDiagonalTailChunk000Sub001Block003Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part008] using hcert

def TailChunk000Sub001Block003Part009SupportExplicit : Finset ℕ :=
  ([8411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part009 : ℚ :=
  (657136958875 : ℚ) / 1504979778684423168

def SurrogateDiagonalTailChunk000Sub001Block003Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8411
    = surrogateDiagTailX0RatChunk000Sub001Block003Part009

theorem surrogateDiagonalTailChunk000Sub001Block003Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part009] using hcert

def TailChunk000Sub001Block003Part010SupportExplicit : Finset ℕ :=
  ([8413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part010 : ℚ :=
  (30859214625 : ℚ) / 81444002476399936

def SurrogateDiagonalTailChunk000Sub001Block003Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8413
    = surrogateDiagTailX0RatChunk000Sub001Block003Part010

theorem surrogateDiagonalTailChunk000Sub001Block003Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part010] using hcert

def TailChunk000Sub001Block003Part011SupportExplicit : Finset ℕ :=
  ([8414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part011 : ℚ :=
  (17796122731 : ℚ) / 4199879808000000

def SurrogateDiagonalTailChunk000Sub001Block003Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8414
    = surrogateDiagTailX0RatChunk000Sub001Block003Part011

theorem surrogateDiagonalTailChunk000Sub001Block003Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part011] using hcert

def TailChunk000Sub001Block003Part012SupportExplicit : Finset ℕ :=
  ([8417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part012 : ℚ :=
  (46555194925 : ℚ) / 3339525023000390016

def SurrogateDiagonalTailChunk000Sub001Block003Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8417
    = surrogateDiagTailX0RatChunk000Sub001Block003Part012

theorem surrogateDiagonalTailChunk000Sub001Block003Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part012] using hcert

def TailChunk000Sub001Block003Part013SupportExplicit : Finset ℕ :=
  ([8418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part013 : ℚ :=
  (1170617263 : ℚ) / 202437663436800

def SurrogateDiagonalTailChunk000Sub001Block003Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8418
    = surrogateDiagTailX0RatChunk000Sub001Block003Part013

theorem surrogateDiagonalTailChunk000Sub001Block003Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part013] using hcert

def TailChunk000Sub001Block003Part014SupportExplicit : Finset ℕ :=
  ([8419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8419
    = surrogateDiagTailX0RatChunk000Sub001Block003Part014

theorem surrogateDiagonalTailChunk000Sub001Block003Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part014] using hcert

def TailChunk000Sub001Block003Part015SupportExplicit : Finset ℕ :=
  ([8421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part015 : ℚ :=
  (894508909 : ℚ) / 1966473216000000

def SurrogateDiagonalTailChunk000Sub001Block003Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8421
    = surrogateDiagTailX0RatChunk000Sub001Block003Part015

theorem surrogateDiagonalTailChunk000Sub001Block003Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part015] using hcert

def TailChunk000Sub001Block003Part016SupportExplicit : Finset ℕ :=
  ([8422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part016 : ℚ :=
  (443313025 : ℚ) / 314206549554162

def SurrogateDiagonalTailChunk000Sub001Block003Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8422
    = surrogateDiagTailX0RatChunk000Sub001Block003Part016

theorem surrogateDiagonalTailChunk000Sub001Block003Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part016] using hcert

def TailChunk000Sub001Block003Part017SupportExplicit : Finset ℕ :=
  ([8423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8423
    = surrogateDiagTailX0RatChunk000Sub001Block003Part017

theorem surrogateDiagonalTailChunk000Sub001Block003Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part017] using hcert

def TailChunk000Sub001Block003Part018SupportExplicit : Finset ℕ :=
  ([8426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part018 : ℚ :=
  (40991455261 : ℚ) / 21298072538755200

def SurrogateDiagonalTailChunk000Sub001Block003Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8426
    = surrogateDiagTailX0RatChunk000Sub001Block003Part018

theorem surrogateDiagonalTailChunk000Sub001Block003Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part018] using hcert

def TailChunk000Sub001Block003Part019SupportExplicit : Finset ℕ :=
  ([8429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8429
    = surrogateDiagTailX0RatChunk000Sub001Block003Part019

theorem surrogateDiagonalTailChunk000Sub001Block003Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part019] using hcert

def TailChunk000Sub001Block003Part020SupportExplicit : Finset ℕ :=
  ([8430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part020 : ℚ :=
  (4623371103 : ℚ) / 419689083699200

def SurrogateDiagonalTailChunk000Sub001Block003Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8430
    = surrogateDiagTailX0RatChunk000Sub001Block003Part020

theorem surrogateDiagonalTailChunk000Sub001Block003Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part020] using hcert

def TailChunk000Sub001Block003Part021SupportExplicit : Finset ℕ :=
  ([8431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block003Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8431
    = surrogateDiagTailX0RatChunk000Sub001Block003Part021

theorem surrogateDiagonalTailChunk000Sub001Block003Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part021] using hcert

def TailChunk000Sub001Block003Part022SupportExplicit : Finset ℕ :=
  ([8434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part022 : ℚ :=
  (277860765625 : ℚ) / 197500989748449792

def SurrogateDiagonalTailChunk000Sub001Block003Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8434
    = surrogateDiagTailX0RatChunk000Sub001Block003Part022

theorem surrogateDiagonalTailChunk000Sub001Block003Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part022] using hcert

def TailChunk000Sub001Block003Part023SupportExplicit : Finset ℕ :=
  ([8435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part023 : ℚ :=
  (7307845087 : ℚ) / 27524332309708800

def SurrogateDiagonalTailChunk000Sub001Block003Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8435
    = surrogateDiagTailX0RatChunk000Sub001Block003Part023

theorem surrogateDiagonalTailChunk000Sub001Block003Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part023] using hcert

def TailChunk000Sub001Block003Part024SupportExplicit : Finset ℕ :=
  ([8437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block003Part024 : ℚ :=
  (17278876273 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk000Sub001Block003Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8437
    = surrogateDiagTailX0RatChunk000Sub001Block003Part024

theorem surrogateDiagonalTailChunk000Sub001Block003Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block003Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block003Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block003Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block003Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block003Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block003HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block003Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part000
    + surrogateDiagTailX0RatChunk000Sub001Block003Part001
    + surrogateDiagTailX0RatChunk000Sub001Block003Part002
    + surrogateDiagTailX0RatChunk000Sub001Block003Part003
    + surrogateDiagTailX0RatChunk000Sub001Block003Part004
    + surrogateDiagTailX0RatChunk000Sub001Block003Part005
    + surrogateDiagTailX0RatChunk000Sub001Block003Part006
    + surrogateDiagTailX0RatChunk000Sub001Block003Part007
    + surrogateDiagTailX0RatChunk000Sub001Block003Part008
    + surrogateDiagTailX0RatChunk000Sub001Block003Part009

def surrogateDiagonalTailChunk000Sub001Block003MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block003Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part010
    + surrogateDiagTailX0RatChunk000Sub001Block003Part011
    + surrogateDiagTailX0RatChunk000Sub001Block003Part012
    + surrogateDiagTailX0RatChunk000Sub001Block003Part013
    + surrogateDiagTailX0RatChunk000Sub001Block003Part014
    + surrogateDiagTailX0RatChunk000Sub001Block003Part015
    + surrogateDiagTailX0RatChunk000Sub001Block003Part016
    + surrogateDiagTailX0RatChunk000Sub001Block003Part017
    + surrogateDiagTailX0RatChunk000Sub001Block003Part018
    + surrogateDiagTailX0RatChunk000Sub001Block003Part019

def surrogateDiagonalTailChunk000Sub001Block003TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block003Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part020
    + surrogateDiagTailX0RatChunk000Sub001Block003Part021
    + surrogateDiagTailX0RatChunk000Sub001Block003Part022
    + surrogateDiagTailX0RatChunk000Sub001Block003Part023
    + surrogateDiagTailX0RatChunk000Sub001Block003Part024

def surrogateDiagonalTailChunk000Sub001Block003Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block003HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block003MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block003TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block003 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block003Part000
    + surrogateDiagTailX0RatChunk000Sub001Block003Part001
    + surrogateDiagTailX0RatChunk000Sub001Block003Part002
    + surrogateDiagTailX0RatChunk000Sub001Block003Part003
    + surrogateDiagTailX0RatChunk000Sub001Block003Part004
    + surrogateDiagTailX0RatChunk000Sub001Block003Part005
    + surrogateDiagTailX0RatChunk000Sub001Block003Part006
    + surrogateDiagTailX0RatChunk000Sub001Block003Part007
    + surrogateDiagTailX0RatChunk000Sub001Block003Part008
    + surrogateDiagTailX0RatChunk000Sub001Block003Part009
    + surrogateDiagTailX0RatChunk000Sub001Block003Part010
    + surrogateDiagTailX0RatChunk000Sub001Block003Part011
    + surrogateDiagTailX0RatChunk000Sub001Block003Part012
    + surrogateDiagTailX0RatChunk000Sub001Block003Part013
    + surrogateDiagTailX0RatChunk000Sub001Block003Part014
    + surrogateDiagTailX0RatChunk000Sub001Block003Part015
    + surrogateDiagTailX0RatChunk000Sub001Block003Part016
    + surrogateDiagTailX0RatChunk000Sub001Block003Part017
    + surrogateDiagTailX0RatChunk000Sub001Block003Part018
    + surrogateDiagTailX0RatChunk000Sub001Block003Part019
    + surrogateDiagTailX0RatChunk000Sub001Block003Part020
    + surrogateDiagTailX0RatChunk000Sub001Block003Part021
    + surrogateDiagTailX0RatChunk000Sub001Block003Part022
    + surrogateDiagTailX0RatChunk000Sub001Block003Part023
    + surrogateDiagTailX0RatChunk000Sub001Block003Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block003_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block003Head + surrogateDiagTailX0RatChunk000Sub001Block003Mid + surrogateDiagTailX0RatChunk000Sub001Block003Tail =
      surrogateDiagTailX0RatChunk000Sub001Block003 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block003Head surrogateDiagTailX0RatChunk000Sub001Block003Mid surrogateDiagTailX0RatChunk000Sub001Block003Tail surrogateDiagTailX0RatChunk000Sub001Block003
  ring

def SurrogateDiagonalTailChunk000Sub001Block003HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block003HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block003Head

def SurrogateDiagonalTailChunk000Sub001Block003MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block003MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block003Mid

def SurrogateDiagonalTailChunk000Sub001Block003TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block003TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block003Tail

theorem surrogateDiagonalTailChunk000Sub001Block003_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block003HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block003MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block003TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block003Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block003 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block003HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block003MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block003TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block003Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block003_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [7,8). -/

/- Block 007 covers tail-support indices [175,200) and q from 337 to 382. -/

def TailChunk000Sub000Block007Part000SupportExplicit : Finset ℕ :=
  ([337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part000 : ℚ :=
  (3932326625 : ℚ) / 1180375547904

def SurrogateDiagonalTailChunk000Sub000Block007Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 337
    = surrogateDiagTailX0RatChunk000Sub000Block007Part000

theorem surrogateDiagonalTailChunk000Sub000Block007Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part000] using hcert

def TailChunk000Sub000Block007Part001SupportExplicit : Finset ℕ :=
  ([339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part001 : ℚ :=
  (508425 : ℚ) / 44957696

def SurrogateDiagonalTailChunk000Sub000Block007Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 339
    = surrogateDiagTailX0RatChunk000Sub000Block007Part001

theorem surrogateDiagonalTailChunk000Sub000Block007Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part001] using hcert

def TailChunk000Sub000Block007Part002SupportExplicit : Finset ℕ :=
  ([341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part002 : ℚ :=
  (3602693479 : ℚ) / 810162000000

def SurrogateDiagonalTailChunk000Sub000Block007Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 341
    = surrogateDiagTailX0RatChunk000Sub000Block007Part002

theorem surrogateDiagonalTailChunk000Sub000Block007Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part002] using hcert

def TailChunk000Sub000Block007Part003SupportExplicit : Finset ℕ :=
  ([345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part003 : ℚ :=
  (54523605025 : ℚ) / 2399261196288

def SurrogateDiagonalTailChunk000Sub000Block007Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 345
    = surrogateDiagTailX0RatChunk000Sub000Block007Part003

theorem surrogateDiagonalTailChunk000Sub000Block007Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part003] using hcert

def TailChunk000Sub000Block007Part004SupportExplicit : Finset ℕ :=
  ([346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part004 : ℚ :=
  (26971266575 : ℚ) / 1094235123264

def SurrogateDiagonalTailChunk000Sub000Block007Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 346
    = surrogateDiagTailX0RatChunk000Sub000Block007Part004

theorem surrogateDiagonalTailChunk000Sub000Block007Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part004] using hcert

def TailChunk000Sub000Block007Part005SupportExplicit : Finset ℕ :=
  ([347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part005 : ℚ :=
  (37522454625 : ℚ) / 11945655866776

def SurrogateDiagonalTailChunk000Sub000Block007Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 347
    = surrogateDiagTailX0RatChunk000Sub000Block007Part005

theorem surrogateDiagonalTailChunk000Sub000Block007Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part005] using hcert

def TailChunk000Sub000Block007Part006SupportExplicit : Finset ℕ :=
  ([349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part006 : ℚ :=
  (106298777725 : ℚ) / 36672780129408

def SurrogateDiagonalTailChunk000Sub000Block007Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 349
    = surrogateDiagTailX0RatChunk000Sub000Block007Part006

theorem surrogateDiagonalTailChunk000Sub000Block007Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part006] using hcert

def TailChunk000Sub000Block007Part007SupportExplicit : Finset ℕ :=
  ([353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part007 : ℚ :=
  (108749389525 : ℚ) / 38388179140608

def SurrogateDiagonalTailChunk000Sub000Block007Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 353
    = surrogateDiagTailX0RatChunk000Sub000Block007Part007

theorem surrogateDiagonalTailChunk000Sub000Block007Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part007] using hcert

def TailChunk000Sub000Block007Part008SupportExplicit : Finset ℕ :=
  ([354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part008 : ℚ :=
  (36784556425 : ℚ) / 452750371968

def SurrogateDiagonalTailChunk000Sub000Block007Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 354
    = surrogateDiagTailX0RatChunk000Sub000Block007Part008

theorem surrogateDiagonalTailChunk000Sub000Block007Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part008] using hcert

def TailChunk000Sub000Block007Part009SupportExplicit : Finset ℕ :=
  ([355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part009 : ℚ :=
  (3551057 : ℚ) / 627325440

def SurrogateDiagonalTailChunk000Sub000Block007Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 355
    = surrogateDiagTailX0RatChunk000Sub000Block007Part009

theorem surrogateDiagonalTailChunk000Sub000Block007Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part009] using hcert

def TailChunk000Sub000Block007Part010SupportExplicit : Finset ℕ :=
  ([357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part010 : ℚ :=
  (3998425 : ℚ) / 226492416

def SurrogateDiagonalTailChunk000Sub000Block007Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 357
    = surrogateDiagTailX0RatChunk000Sub000Block007Part010

theorem surrogateDiagonalTailChunk000Sub000Block007Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part010] using hcert

def TailChunk000Sub000Block007Part011SupportExplicit : Finset ℕ :=
  ([358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part011 : ℚ :=
  (27884481275 : ℚ) / 1255095788964

def SurrogateDiagonalTailChunk000Sub000Block007Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 358
    = surrogateDiagTailX0RatChunk000Sub000Block007Part011

theorem surrogateDiagonalTailChunk000Sub000Block007Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part011] using hcert

def TailChunk000Sub000Block007Part012SupportExplicit : Finset ℕ :=
  ([359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part012 : ℚ :=
  (112477670725 : ℚ) / 41073240245448

def SurrogateDiagonalTailChunk000Sub000Block007Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 359
    = surrogateDiagTailX0RatChunk000Sub000Block007Part012

theorem surrogateDiagonalTailChunk000Sub000Block007Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part012] using hcert

def TailChunk000Sub000Block007Part013SupportExplicit : Finset ℕ :=
  ([362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part013 : ℚ :=
  (1140443171 : ℚ) / 52498497600

def SurrogateDiagonalTailChunk000Sub000Block007Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 362
    = surrogateDiagTailX0RatChunk000Sub000Block007Part013

theorem surrogateDiagonalTailChunk000Sub000Block007Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part013] using hcert

def TailChunk000Sub000Block007Part014SupportExplicit : Finset ℕ :=
  ([365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part014 : ℚ :=
  (91323634075 : ℚ) / 17202707693568

def SurrogateDiagonalTailChunk000Sub000Block007Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 365
    = surrogateDiagTailX0RatChunk000Sub000Block007Part014

theorem surrogateDiagonalTailChunk000Sub000Block007Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part014] using hcert

def TailChunk000Sub000Block007Part015SupportExplicit : Finset ℕ :=
  ([366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part015 : ℚ :=
  (1491893959 : ℚ) / 20740147200

def SurrogateDiagonalTailChunk000Sub000Block007Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 366
    = surrogateDiagTailX0RatChunk000Sub000Block007Part015

theorem surrogateDiagonalTailChunk000Sub000Block007Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part015] using hcert

def TailChunk000Sub000Block007Part016SupportExplicit : Finset ℕ :=
  ([367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part016 : ℚ :=
  (117546457525 : ℚ) / 44869496944968

def SurrogateDiagonalTailChunk000Sub000Block007Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 367
    = surrogateDiagTailX0RatChunk000Sub000Block007Part016

theorem surrogateDiagonalTailChunk000Sub000Block007Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part016] using hcert

def TailChunk000Sub000Block007Part017SupportExplicit : Finset ℕ :=
  ([370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part017 : ℚ :=
  (22483120625 : ℚ) / 537584615424

def SurrogateDiagonalTailChunk000Sub000Block007Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 370
    = surrogateDiagTailX0RatChunk000Sub000Block007Part017

theorem surrogateDiagonalTailChunk000Sub000Block007Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part017] using hcert

def TailChunk000Sub000Block007Part018SupportExplicit : Finset ℕ :=
  ([371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part018 : ℚ :=
  (11191409725 : ℚ) / 2632708196352

def SurrogateDiagonalTailChunk000Sub000Block007Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 371
    = surrogateDiagTailX0RatChunk000Sub000Block007Part018

theorem surrogateDiagonalTailChunk000Sub000Block007Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part018] using hcert

def TailChunk000Sub000Block007Part019SupportExplicit : Finset ℕ :=
  ([373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part019 : ℚ :=
  (56385505475 : ℚ) / 23942451852864

def SurrogateDiagonalTailChunk000Sub000Block007Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 373
    = surrogateDiagTailX0RatChunk000Sub000Block007Part019

theorem surrogateDiagonalTailChunk000Sub000Block007Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part019] using hcert

def TailChunk000Sub000Block007Part020SupportExplicit : Finset ℕ :=
  ([374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part020 : ℚ :=
  (2016979711 : ℚ) / 65549107200

def SurrogateDiagonalTailChunk000Sub000Block007Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 374
    = surrogateDiagTailX0RatChunk000Sub000Block007Part020

theorem surrogateDiagonalTailChunk000Sub000Block007Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part020] using hcert

def TailChunk000Sub000Block007Part021SupportExplicit : Finset ℕ :=
  ([377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part021 : ℚ :=
  (25791522025 : ℚ) / 7967534948352

def SurrogateDiagonalTailChunk000Sub000Block007Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 377
    = surrogateDiagTailX0RatChunk000Sub000Block007Part021

theorem surrogateDiagonalTailChunk000Sub000Block007Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part021] using hcert

def TailChunk000Sub000Block007Part022SupportExplicit : Finset ℕ :=
  ([379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part022 : ℚ :=
  (58214106275 : ℚ) / 25524900779364

def SurrogateDiagonalTailChunk000Sub000Block007Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 379
    = surrogateDiagTailX0RatChunk000Sub000Block007Part022

theorem surrogateDiagonalTailChunk000Sub000Block007Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part022] using hcert

def TailChunk000Sub000Block007Part023SupportExplicit : Finset ℕ :=
  ([381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part023 : ℚ :=
  (2600525 : ℚ) / 336063168

def SurrogateDiagonalTailChunk000Sub000Block007Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 381
    = surrogateDiagTailX0RatChunk000Sub000Block007Part023

theorem surrogateDiagonalTailChunk000Sub000Block007Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part023] using hcert

def TailChunk000Sub000Block007Part024SupportExplicit : Finset ℕ :=
  ([382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block007Part024 : ℚ :=
  (94376347 : ℚ) / 5213882568

def SurrogateDiagonalTailChunk000Sub000Block007Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 382
    = surrogateDiagTailX0RatChunk000Sub000Block007Part024

theorem surrogateDiagonalTailChunk000Sub000Block007Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block007Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block007Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block007Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block007Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block007Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block007HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block007Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block007Part000
    + surrogateDiagTailX0RatChunk000Sub000Block007Part001
    + surrogateDiagTailX0RatChunk000Sub000Block007Part002
    + surrogateDiagTailX0RatChunk000Sub000Block007Part003
    + surrogateDiagTailX0RatChunk000Sub000Block007Part004
    + surrogateDiagTailX0RatChunk000Sub000Block007Part005
    + surrogateDiagTailX0RatChunk000Sub000Block007Part006
    + surrogateDiagTailX0RatChunk000Sub000Block007Part007
    + surrogateDiagTailX0RatChunk000Sub000Block007Part008
    + surrogateDiagTailX0RatChunk000Sub000Block007Part009

def surrogateDiagonalTailChunk000Sub000Block007MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block007Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block007Part010
    + surrogateDiagTailX0RatChunk000Sub000Block007Part011
    + surrogateDiagTailX0RatChunk000Sub000Block007Part012
    + surrogateDiagTailX0RatChunk000Sub000Block007Part013
    + surrogateDiagTailX0RatChunk000Sub000Block007Part014
    + surrogateDiagTailX0RatChunk000Sub000Block007Part015
    + surrogateDiagTailX0RatChunk000Sub000Block007Part016
    + surrogateDiagTailX0RatChunk000Sub000Block007Part017
    + surrogateDiagTailX0RatChunk000Sub000Block007Part018
    + surrogateDiagTailX0RatChunk000Sub000Block007Part019

def surrogateDiagonalTailChunk000Sub000Block007TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block007Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block007Part020
    + surrogateDiagTailX0RatChunk000Sub000Block007Part021
    + surrogateDiagTailX0RatChunk000Sub000Block007Part022
    + surrogateDiagTailX0RatChunk000Sub000Block007Part023
    + surrogateDiagTailX0RatChunk000Sub000Block007Part024

def surrogateDiagonalTailChunk000Sub000Block007Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block007HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block007MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block007TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block007 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block007Part000
    + surrogateDiagTailX0RatChunk000Sub000Block007Part001
    + surrogateDiagTailX0RatChunk000Sub000Block007Part002
    + surrogateDiagTailX0RatChunk000Sub000Block007Part003
    + surrogateDiagTailX0RatChunk000Sub000Block007Part004
    + surrogateDiagTailX0RatChunk000Sub000Block007Part005
    + surrogateDiagTailX0RatChunk000Sub000Block007Part006
    + surrogateDiagTailX0RatChunk000Sub000Block007Part007
    + surrogateDiagTailX0RatChunk000Sub000Block007Part008
    + surrogateDiagTailX0RatChunk000Sub000Block007Part009
    + surrogateDiagTailX0RatChunk000Sub000Block007Part010
    + surrogateDiagTailX0RatChunk000Sub000Block007Part011
    + surrogateDiagTailX0RatChunk000Sub000Block007Part012
    + surrogateDiagTailX0RatChunk000Sub000Block007Part013
    + surrogateDiagTailX0RatChunk000Sub000Block007Part014
    + surrogateDiagTailX0RatChunk000Sub000Block007Part015
    + surrogateDiagTailX0RatChunk000Sub000Block007Part016
    + surrogateDiagTailX0RatChunk000Sub000Block007Part017
    + surrogateDiagTailX0RatChunk000Sub000Block007Part018
    + surrogateDiagTailX0RatChunk000Sub000Block007Part019
    + surrogateDiagTailX0RatChunk000Sub000Block007Part020
    + surrogateDiagTailX0RatChunk000Sub000Block007Part021
    + surrogateDiagTailX0RatChunk000Sub000Block007Part022
    + surrogateDiagTailX0RatChunk000Sub000Block007Part023
    + surrogateDiagTailX0RatChunk000Sub000Block007Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block007_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block007Head + surrogateDiagTailX0RatChunk000Sub000Block007Mid + surrogateDiagTailX0RatChunk000Sub000Block007Tail =
      surrogateDiagTailX0RatChunk000Sub000Block007 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block007Head surrogateDiagTailX0RatChunk000Sub000Block007Mid surrogateDiagTailX0RatChunk000Sub000Block007Tail surrogateDiagTailX0RatChunk000Sub000Block007
  ring

def SurrogateDiagonalTailChunk000Sub000Block007HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block007HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block007Head

def SurrogateDiagonalTailChunk000Sub000Block007MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block007MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block007Mid

def SurrogateDiagonalTailChunk000Sub000Block007TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block007TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block007Tail

theorem surrogateDiagonalTailChunk000Sub000Block007_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block007HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block007MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block007TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block007Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block007 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block007HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block007MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block007TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block007Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block007_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [95,96). -/

/- Block 095 covers tail-support indices [2375,2400) and q from 3957 to 3997. -/

def TailChunk000Sub000Block095Part000SupportExplicit : Finset ℕ :=
  ([3957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part000 : ℚ :=
  (65204625 : ℚ) / 12070399165504

def SurrogateDiagonalTailChunk000Sub000Block095Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3957
    = surrogateDiagTailX0RatChunk000Sub000Block095Part000

theorem surrogateDiagonalTailChunk000Sub000Block095Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part000] using hcert

def TailChunk000Sub000Block095Part001SupportExplicit : Finset ℕ :=
  ([3958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part001 : ℚ :=
  (244679651475 : ℚ) / 12758827130388376

def SurrogateDiagonalTailChunk000Sub000Block095Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3958
    = surrogateDiagTailX0RatChunk000Sub000Block095Part001

theorem surrogateDiagonalTailChunk000Sub000Block095Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part001] using hcert

def TailChunk000Sub000Block095Part002SupportExplicit : Finset ℕ :=
  ([3959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part002 : ℚ :=
  (476875656875 : ℚ) / 265112574618461184

def SurrogateDiagonalTailChunk000Sub000Block095Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3959
    = surrogateDiagTailX0RatChunk000Sub000Block095Part002

theorem surrogateDiagonalTailChunk000Sub000Block095Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part002] using hcert

def TailChunk000Sub000Block095Part003SupportExplicit : Finset ℕ :=
  ([3961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part003 : ℚ :=
  (936979358725 : ℚ) / 474743174036717568

def SurrogateDiagonalTailChunk000Sub000Block095Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3961
    = surrogateDiagTailX0RatChunk000Sub000Block095Part003

theorem surrogateDiagonalTailChunk000Sub000Block095Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part003] using hcert

def TailChunk000Sub000Block095Part004SupportExplicit : Finset ℕ :=
  ([3962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part004 : ℚ :=
  (439322854675 : ℚ) / 20494073701381248

def SurrogateDiagonalTailChunk000Sub000Block095Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3962
    = surrogateDiagTailX0RatChunk000Sub000Block095Part004

theorem surrogateDiagonalTailChunk000Sub000Block095Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part004] using hcert

def TailChunk000Sub000Block095Part005SupportExplicit : Finset ℕ :=
  ([3963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part005 : ℚ :=
  (30522218377 : ℚ) / 4858503922483200

def SurrogateDiagonalTailChunk000Sub000Block095Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3963
    = surrogateDiagTailX0RatChunk000Sub000Block095Part005

theorem surrogateDiagonalTailChunk000Sub000Block095Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part005] using hcert

def TailChunk000Sub000Block095Part006SupportExplicit : Finset ℕ :=
  ([3965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part006 : ℚ :=
  (30523158511 : ℚ) / 6881083077427200

def SurrogateDiagonalTailChunk000Sub000Block095Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3965
    = surrogateDiagTailX0RatChunk000Sub000Block095Part006

theorem surrogateDiagonalTailChunk000Sub000Block095Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part006] using hcert

def TailChunk000Sub000Block095Part007SupportExplicit : Finset ℕ :=
  ([3966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part007 : ℚ :=
  (7092295217 : ℚ) / 151828247577600

def SurrogateDiagonalTailChunk000Sub000Block095Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3966
    = surrogateDiagTailX0RatChunk000Sub000Block095Part007

theorem surrogateDiagonalTailChunk000Sub000Block095Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part007] using hcert

def TailChunk000Sub000Block095Part008SupportExplicit : Finset ℕ :=
  ([3967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part008 : ℚ :=
  (245892015625 : ℚ) / 154659893588769042

def SurrogateDiagonalTailChunk000Sub000Block095Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3967
    = surrogateDiagTailX0RatChunk000Sub000Block095Part008

theorem surrogateDiagonalTailChunk000Sub000Block095Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part008] using hcert

def TailChunk000Sub000Block095Part009SupportExplicit : Finset ℕ :=
  ([3970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part009 : ℚ :=
  (569811514825 : ℚ) / 15741552708845568

def SurrogateDiagonalTailChunk000Sub000Block095Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3970
    = surrogateDiagTailX0RatChunk000Sub000Block095Part009

theorem surrogateDiagonalTailChunk000Sub000Block095Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part009] using hcert

def TailChunk000Sub000Block095Part010SupportExplicit : Finset ℕ :=
  ([3973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part010 : ℚ :=
  (109527386075 : ℚ) / 30928987023212544

def SurrogateDiagonalTailChunk000Sub000Block095Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3973
    = surrogateDiagTailX0RatChunk000Sub000Block095Part010

theorem surrogateDiagonalTailChunk000Sub000Block095Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part010] using hcert

def TailChunk000Sub000Block095Part011SupportExplicit : Finset ℕ :=
  ([3974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part011 : ℚ :=
  (82220619425 : ℚ) / 4322164839675912

def SurrogateDiagonalTailChunk000Sub000Block095Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3974
    = surrogateDiagTailX0RatChunk000Sub000Block095Part011

theorem surrogateDiagonalTailChunk000Sub000Block095Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part011] using hcert

def TailChunk000Sub000Block095Part012SupportExplicit : Finset ℕ :=
  ([3977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part012 : ℚ :=
  (1284741557 : ℚ) / 724920686346240

def SurrogateDiagonalTailChunk000Sub000Block095Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3977
    = surrogateDiagTailX0RatChunk000Sub000Block095Part012

theorem surrogateDiagonalTailChunk000Sub000Block095Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part012] using hcert

def TailChunk000Sub000Block095Part013SupportExplicit : Finset ℕ :=
  ([3979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part013 : ℚ :=
  (476848372025 : ℚ) / 256331143035331584

def SurrogateDiagonalTailChunk000Sub000Block095Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3979
    = surrogateDiagTailX0RatChunk000Sub000Block095Part013

theorem surrogateDiagonalTailChunk000Sub000Block095Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part013] using hcert

def TailChunk000Sub000Block095Part014SupportExplicit : Finset ℕ :=
  ([3981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part014 : ℚ :=
  (770002399975 : ℚ) / 123686111962977408

def SurrogateDiagonalTailChunk000Sub000Block095Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3981
    = surrogateDiagTailX0RatChunk000Sub000Block095Part014

theorem surrogateDiagonalTailChunk000Sub000Block095Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part014] using hcert

def TailChunk000Sub000Block095Part015SupportExplicit : Finset ℕ :=
  ([3982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part015 : ℚ :=
  (921682103 : ℚ) / 52498497600000

def SurrogateDiagonalTailChunk000Sub000Block095Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3982
    = surrogateDiagTailX0RatChunk000Sub000Block095Part015

theorem surrogateDiagonalTailChunk000Sub000Block095Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part015] using hcert

def TailChunk000Sub000Block095Part016SupportExplicit : Finset ℕ :=
  ([3983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part016 : ℚ :=
  (889249402225 : ℚ) / 337306882905243648

def SurrogateDiagonalTailChunk000Sub000Block095Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3983
    = surrogateDiagTailX0RatChunk000Sub000Block095Part016

theorem surrogateDiagonalTailChunk000Sub000Block095Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part016] using hcert

def TailChunk000Sub000Block095Part017SupportExplicit : Finset ℕ :=
  ([3985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part017 : ℚ :=
  (277676413875 : ℚ) / 85663899584659456

def SurrogateDiagonalTailChunk000Sub000Block095Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3985
    = surrogateDiagTailX0RatChunk000Sub000Block095Part017

theorem surrogateDiagonalTailChunk000Sub000Block095Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part017] using hcert

def TailChunk000Sub000Block095Part018SupportExplicit : Finset ℕ :=
  ([3986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part018 : ℚ :=
  (82717920425 : ℚ) / 4374633615132672

def SurrogateDiagonalTailChunk000Sub000Block095Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3986
    = surrogateDiagTailX0RatChunk000Sub000Block095Part018

theorem surrogateDiagonalTailChunk000Sub000Block095Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part018] using hcert

def TailChunk000Sub000Block095Part019SupportExplicit : Finset ℕ :=
  ([3989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part019 : ℚ :=
  (248626890625 : ℚ) / 158120240457506592

def SurrogateDiagonalTailChunk000Sub000Block095Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3989
    = surrogateDiagTailX0RatChunk000Sub000Block095Part019

theorem surrogateDiagonalTailChunk000Sub000Block095Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part019] using hcert

def TailChunk000Sub000Block095Part020SupportExplicit : Finset ℕ :=
  ([3990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part020 : ℚ :=
  (6013966475 : ℚ) / 29029569232896

def SurrogateDiagonalTailChunk000Sub000Block095Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3990
    = surrogateDiagTailX0RatChunk000Sub000Block095Part020

theorem surrogateDiagonalTailChunk000Sub000Block095Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part020] using hcert

def TailChunk000Sub000Block095Part021SupportExplicit : Finset ℕ :=
  ([3991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part021 : ℚ :=
  (467213733725 : ℚ) / 227304248615691264

def SurrogateDiagonalTailChunk000Sub000Block095Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3991
    = surrogateDiagTailX0RatChunk000Sub000Block095Part021

theorem surrogateDiagonalTailChunk000Sub000Block095Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part021] using hcert

def TailChunk000Sub000Block095Part022SupportExplicit : Finset ℕ :=
  ([3994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part022 : ℚ :=
  (498401424775 : ℚ) / 39688894912384128

def SurrogateDiagonalTailChunk000Sub000Block095Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3994
    = surrogateDiagTailX0RatChunk000Sub000Block095Part022

theorem surrogateDiagonalTailChunk000Sub000Block095Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part022] using hcert

def TailChunk000Sub000Block095Part023SupportExplicit : Finset ℕ :=
  ([3995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part023 : ℚ :=
  (817397001625 : ℚ) / 187835675729461248

def SurrogateDiagonalTailChunk000Sub000Block095Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3995
    = surrogateDiagTailX0RatChunk000Sub000Block095Part023

theorem surrogateDiagonalTailChunk000Sub000Block095Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part023] using hcert

def TailChunk000Sub000Block095Part024SupportExplicit : Finset ℕ :=
  ([3997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block095Part024 : ℚ :=
  (35820381613 : ℚ) / 13683313411459200

def SurrogateDiagonalTailChunk000Sub000Block095Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3997
    = surrogateDiagTailX0RatChunk000Sub000Block095Part024

theorem surrogateDiagonalTailChunk000Sub000Block095Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block095Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block095Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block095Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block095Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block095Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block095HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block095Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block095Part000
    + surrogateDiagTailX0RatChunk000Sub000Block095Part001
    + surrogateDiagTailX0RatChunk000Sub000Block095Part002
    + surrogateDiagTailX0RatChunk000Sub000Block095Part003
    + surrogateDiagTailX0RatChunk000Sub000Block095Part004
    + surrogateDiagTailX0RatChunk000Sub000Block095Part005
    + surrogateDiagTailX0RatChunk000Sub000Block095Part006
    + surrogateDiagTailX0RatChunk000Sub000Block095Part007
    + surrogateDiagTailX0RatChunk000Sub000Block095Part008
    + surrogateDiagTailX0RatChunk000Sub000Block095Part009

def surrogateDiagonalTailChunk000Sub000Block095MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block095Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block095Part010
    + surrogateDiagTailX0RatChunk000Sub000Block095Part011
    + surrogateDiagTailX0RatChunk000Sub000Block095Part012
    + surrogateDiagTailX0RatChunk000Sub000Block095Part013
    + surrogateDiagTailX0RatChunk000Sub000Block095Part014
    + surrogateDiagTailX0RatChunk000Sub000Block095Part015
    + surrogateDiagTailX0RatChunk000Sub000Block095Part016
    + surrogateDiagTailX0RatChunk000Sub000Block095Part017
    + surrogateDiagTailX0RatChunk000Sub000Block095Part018
    + surrogateDiagTailX0RatChunk000Sub000Block095Part019

def surrogateDiagonalTailChunk000Sub000Block095TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block095Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block095Part020
    + surrogateDiagTailX0RatChunk000Sub000Block095Part021
    + surrogateDiagTailX0RatChunk000Sub000Block095Part022
    + surrogateDiagTailX0RatChunk000Sub000Block095Part023
    + surrogateDiagTailX0RatChunk000Sub000Block095Part024

def surrogateDiagonalTailChunk000Sub000Block095Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block095HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block095MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block095TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block095 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block095Part000
    + surrogateDiagTailX0RatChunk000Sub000Block095Part001
    + surrogateDiagTailX0RatChunk000Sub000Block095Part002
    + surrogateDiagTailX0RatChunk000Sub000Block095Part003
    + surrogateDiagTailX0RatChunk000Sub000Block095Part004
    + surrogateDiagTailX0RatChunk000Sub000Block095Part005
    + surrogateDiagTailX0RatChunk000Sub000Block095Part006
    + surrogateDiagTailX0RatChunk000Sub000Block095Part007
    + surrogateDiagTailX0RatChunk000Sub000Block095Part008
    + surrogateDiagTailX0RatChunk000Sub000Block095Part009
    + surrogateDiagTailX0RatChunk000Sub000Block095Part010
    + surrogateDiagTailX0RatChunk000Sub000Block095Part011
    + surrogateDiagTailX0RatChunk000Sub000Block095Part012
    + surrogateDiagTailX0RatChunk000Sub000Block095Part013
    + surrogateDiagTailX0RatChunk000Sub000Block095Part014
    + surrogateDiagTailX0RatChunk000Sub000Block095Part015
    + surrogateDiagTailX0RatChunk000Sub000Block095Part016
    + surrogateDiagTailX0RatChunk000Sub000Block095Part017
    + surrogateDiagTailX0RatChunk000Sub000Block095Part018
    + surrogateDiagTailX0RatChunk000Sub000Block095Part019
    + surrogateDiagTailX0RatChunk000Sub000Block095Part020
    + surrogateDiagTailX0RatChunk000Sub000Block095Part021
    + surrogateDiagTailX0RatChunk000Sub000Block095Part022
    + surrogateDiagTailX0RatChunk000Sub000Block095Part023
    + surrogateDiagTailX0RatChunk000Sub000Block095Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block095_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block095Head + surrogateDiagTailX0RatChunk000Sub000Block095Mid + surrogateDiagTailX0RatChunk000Sub000Block095Tail =
      surrogateDiagTailX0RatChunk000Sub000Block095 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block095Head surrogateDiagTailX0RatChunk000Sub000Block095Mid surrogateDiagTailX0RatChunk000Sub000Block095Tail surrogateDiagTailX0RatChunk000Sub000Block095
  ring

def SurrogateDiagonalTailChunk000Sub000Block095HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block095HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block095Head

def SurrogateDiagonalTailChunk000Sub000Block095MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block095MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block095Mid

def SurrogateDiagonalTailChunk000Sub000Block095TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block095TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block095Tail

theorem surrogateDiagonalTailChunk000Sub000Block095_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block095HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block095MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block095TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block095Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block095 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block095HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block095MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block095TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block095Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block095_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

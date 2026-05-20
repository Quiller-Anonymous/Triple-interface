import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [140,141). -/

/- Block 140 covers tail-support indices [3500,3525) and q from 5811 to 5853. -/

def TailChunk000Sub000Block140Part000SupportExplicit : Finset ℕ :=
  ([5811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part000 : ℚ :=
  (61332363725 : ℚ) / 49754080021118976

def SurrogateDiagonalTailChunk000Sub000Block140Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5811
    = surrogateDiagTailX0RatChunk000Sub000Block140Part000

theorem surrogateDiagonalTailChunk000Sub000Block140Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part000] using hcert

def TailChunk000Sub000Block140Part001SupportExplicit : Finset ℕ :=
  ([5813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block140Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5813
    = surrogateDiagTailX0RatChunk000Sub000Block140Part001

theorem surrogateDiagonalTailChunk000Sub000Block140Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part001] using hcert

def TailChunk000Sub000Block140Part002SupportExplicit : Finset ℕ :=
  ([5815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part002 : ℚ :=
  (844696280375 : ℚ) / 583527517218530304

def SurrogateDiagonalTailChunk000Sub000Block140Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5815
    = surrogateDiagTailX0RatChunk000Sub000Block140Part002

theorem surrogateDiagonalTailChunk000Sub000Block140Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part002] using hcert

def TailChunk000Sub000Block140Part003SupportExplicit : Finset ℕ :=
  ([5817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part003 : ℚ :=
  (19582325 : ℚ) / 5013604491264

def SurrogateDiagonalTailChunk000Sub000Block140Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5817
    = surrogateDiagTailX0RatChunk000Sub000Block140Part003

theorem surrogateDiagonalTailChunk000Sub000Block140Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part003] using hcert

def TailChunk000Sub000Block140Part004SupportExplicit : Finset ℕ :=
  ([5818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part004 : ℚ :=
  (1057573567975 : ℚ) / 178815214349931648

def SurrogateDiagonalTailChunk000Sub000Block140Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5818
    = surrogateDiagTailX0RatChunk000Sub000Block140Part004

theorem surrogateDiagonalTailChunk000Sub000Block140Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part004] using hcert

def TailChunk000Sub000Block140Part005SupportExplicit : Finset ℕ :=
  ([5821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part005 : ℚ :=
  (847101025 : ℚ) / 1147568949656352

def SurrogateDiagonalTailChunk000Sub000Block140Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5821
    = surrogateDiagTailX0RatChunk000Sub000Block140Part005

theorem surrogateDiagonalTailChunk000Sub000Block140Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part005] using hcert

def TailChunk000Sub000Block140Part006SupportExplicit : Finset ℕ :=
  ([5822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part006 : ℚ :=
  (8106554081 : ℚ) / 1229557862400000

def SurrogateDiagonalTailChunk000Sub000Block140Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5822
    = surrogateDiagTailX0RatChunk000Sub000Block140Part006

theorem surrogateDiagonalTailChunk000Sub000Block140Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part006] using hcert

def TailChunk000Sub000Block140Part007SupportExplicit : Finset ℕ :=
  ([5826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part007 : ℚ :=
  (1130079 : ℚ) / 56658739840

def SurrogateDiagonalTailChunk000Sub000Block140Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5826
    = surrogateDiagTailX0RatChunk000Sub000Block140Part007

theorem surrogateDiagonalTailChunk000Sub000Block140Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part007] using hcert

def TailChunk000Sub000Block140Part008SupportExplicit : Finset ℕ :=
  ([5827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part008 : ℚ :=
  (530530140625 : ℚ) / 720192822300117522

def SurrogateDiagonalTailChunk000Sub000Block140Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5827
    = surrogateDiagTailX0RatChunk000Sub000Block140Part008

theorem surrogateDiagonalTailChunk000Sub000Block140Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part008] using hcert

def TailChunk000Sub000Block140Part009SupportExplicit : Finset ℕ :=
  ([5829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part009 : ℚ :=
  (1124029035775 : ℚ) / 466610716715286528

def SurrogateDiagonalTailChunk000Sub000Block140Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5829
    = surrogateDiagTailX0RatChunk000Sub000Block140Part009

theorem surrogateDiagonalTailChunk000Sub000Block140Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part009] using hcert

def TailChunk000Sub000Block140Part010SupportExplicit : Finset ℕ :=
  ([5830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part010 : ℚ :=
  (1166588281 : ℚ) / 74885922029568

def SurrogateDiagonalTailChunk000Sub000Block140Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5830
    = surrogateDiagTailX0RatChunk000Sub000Block140Part010

theorem surrogateDiagonalTailChunk000Sub000Block140Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part010] using hcert

def TailChunk000Sub000Block140Part011SupportExplicit : Finset ℕ :=
  ([5833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part011 : ℚ :=
  (1989900644875 : ℚ) / 2301455517233874048

def SurrogateDiagonalTailChunk000Sub000Block140Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5833
    = surrogateDiagTailX0RatChunk000Sub000Block140Part011

theorem surrogateDiagonalTailChunk000Sub000Block140Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part011] using hcert

def TailChunk000Sub000Block140Part012SupportExplicit : Finset ℕ :=
  ([5834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part012 : ℚ :=
  (1063398402775 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub000Block140Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5834
    = surrogateDiagTailX0RatChunk000Sub000Block140Part012

theorem surrogateDiagonalTailChunk000Sub000Block140Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part012] using hcert

def TailChunk000Sub000Block140Part013SupportExplicit : Finset ℕ :=
  ([5835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part013 : ℚ :=
  (943513874575 : ℚ) / 232120613224316928

def SurrogateDiagonalTailChunk000Sub000Block140Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5835
    = surrogateDiagTailX0RatChunk000Sub000Block140Part013

theorem surrogateDiagonalTailChunk000Sub000Block140Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part013] using hcert

def TailChunk000Sub000Block140Part014SupportExplicit : Finset ℕ :=
  ([5837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part014 : ℚ :=
  (645298996175 : ℚ) / 696213827166928896

def SurrogateDiagonalTailChunk000Sub000Block140Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5837
    = surrogateDiagTailX0RatChunk000Sub000Block140Part014

theorem surrogateDiagonalTailChunk000Sub000Block140Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part014] using hcert

def TailChunk000Sub000Block140Part015SupportExplicit : Finset ℕ :=
  ([5838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part015 : ℚ :=
  (13096025 : ℚ) / 417800374272

def SurrogateDiagonalTailChunk000Sub000Block140Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5838
    = surrogateDiagTailX0RatChunk000Sub000Block140Part015

theorem surrogateDiagonalTailChunk000Sub000Block140Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part015] using hcert

def TailChunk000Sub000Block140Part016SupportExplicit : Finset ℕ :=
  ([5839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part016 : ℚ :=
  (532717515625 : ℚ) / 726144797466719442

def SurrogateDiagonalTailChunk000Sub000Block140Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5839
    = surrogateDiagTailX0RatChunk000Sub000Block140Part016

theorem surrogateDiagonalTailChunk000Sub000Block140Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part016] using hcert

def TailChunk000Sub000Block140Part017SupportExplicit : Finset ℕ :=
  ([5842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part017 : ℚ :=
  (58315441775 : ℚ) / 16404283009521792

def SurrogateDiagonalTailChunk000Sub000Block140Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5842
    = surrogateDiagTailX0RatChunk000Sub000Block140Part017

theorem surrogateDiagonalTailChunk000Sub000Block140Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part017] using hcert

def TailChunk000Sub000Block140Part018SupportExplicit : Finset ℕ :=
  ([5843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part018 : ℚ :=
  (533447640625 : ℚ) / 728136963093774162

def SurrogateDiagonalTailChunk000Sub000Block140Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5843
    = surrogateDiagTailX0RatChunk000Sub000Block140Part018

theorem surrogateDiagonalTailChunk000Sub000Block140Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part018] using hcert

def TailChunk000Sub000Block140Part019SupportExplicit : Finset ℕ :=
  ([5845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part019 : ℚ :=
  (4191231875 : ℚ) / 1944281606725632

def SurrogateDiagonalTailChunk000Sub000Block140Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5845
    = surrogateDiagTailX0RatChunk000Sub000Block140Part019

theorem surrogateDiagonalTailChunk000Sub000Block140Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part019] using hcert

def TailChunk000Sub000Block140Part020SupportExplicit : Finset ℕ :=
  ([5846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part020 : ℚ :=
  (1560907775 : ℚ) / 459937237533696

def SurrogateDiagonalTailChunk000Sub000Block140Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5846
    = surrogateDiagTailX0RatChunk000Sub000Block140Part020

theorem surrogateDiagonalTailChunk000Sub000Block140Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part020] using hcert

def TailChunk000Sub000Block140Part021SupportExplicit : Finset ℕ :=
  ([5847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part021 : ℚ :=
  (142363875 : ℚ) / 57599113790464

def SurrogateDiagonalTailChunk000Sub000Block140Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5847
    = surrogateDiagTailX0RatChunk000Sub000Block140Part021

theorem surrogateDiagonalTailChunk000Sub000Block140Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part021] using hcert

def TailChunk000Sub000Block140Part022SupportExplicit : Finset ℕ :=
  ([5849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part022 : ℚ :=
  (534543765625 : ℚ) / 731132893841060352

def SurrogateDiagonalTailChunk000Sub000Block140Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5849
    = surrogateDiagTailX0RatChunk000Sub000Block140Part022

theorem surrogateDiagonalTailChunk000Sub000Block140Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part022] using hcert

def TailChunk000Sub000Block140Part023SupportExplicit : Finset ℕ :=
  ([5851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part023 : ℚ :=
  (34234201 : ℚ) / 46856549686050

def SurrogateDiagonalTailChunk000Sub000Block140Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5851
    = surrogateDiagTailX0RatChunk000Sub000Block140Part023

theorem surrogateDiagonalTailChunk000Sub000Block140Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part023] using hcert

def TailChunk000Sub000Block140Part024SupportExplicit : Finset ℕ :=
  ([5853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block140Part024 : ℚ :=
  (11890962637 : ℚ) / 5784759220500000

def SurrogateDiagonalTailChunk000Sub000Block140Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5853
    = surrogateDiagTailX0RatChunk000Sub000Block140Part024

theorem surrogateDiagonalTailChunk000Sub000Block140Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block140Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block140Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block140Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block140Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block140Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block140Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block140HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block140Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block140Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block140Part000
    + surrogateDiagTailX0RatChunk000Sub000Block140Part001
    + surrogateDiagTailX0RatChunk000Sub000Block140Part002
    + surrogateDiagTailX0RatChunk000Sub000Block140Part003
    + surrogateDiagTailX0RatChunk000Sub000Block140Part004
    + surrogateDiagTailX0RatChunk000Sub000Block140Part005
    + surrogateDiagTailX0RatChunk000Sub000Block140Part006
    + surrogateDiagTailX0RatChunk000Sub000Block140Part007
    + surrogateDiagTailX0RatChunk000Sub000Block140Part008
    + surrogateDiagTailX0RatChunk000Sub000Block140Part009

def surrogateDiagonalTailChunk000Sub000Block140MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block140Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block140Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block140Part010
    + surrogateDiagTailX0RatChunk000Sub000Block140Part011
    + surrogateDiagTailX0RatChunk000Sub000Block140Part012
    + surrogateDiagTailX0RatChunk000Sub000Block140Part013
    + surrogateDiagTailX0RatChunk000Sub000Block140Part014
    + surrogateDiagTailX0RatChunk000Sub000Block140Part015
    + surrogateDiagTailX0RatChunk000Sub000Block140Part016
    + surrogateDiagTailX0RatChunk000Sub000Block140Part017
    + surrogateDiagTailX0RatChunk000Sub000Block140Part018
    + surrogateDiagTailX0RatChunk000Sub000Block140Part019

def surrogateDiagonalTailChunk000Sub000Block140TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block140Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block140Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block140Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block140Part020
    + surrogateDiagTailX0RatChunk000Sub000Block140Part021
    + surrogateDiagTailX0RatChunk000Sub000Block140Part022
    + surrogateDiagTailX0RatChunk000Sub000Block140Part023
    + surrogateDiagTailX0RatChunk000Sub000Block140Part024

def surrogateDiagonalTailChunk000Sub000Block140Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block140HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block140MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block140TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block140 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block140Part000
    + surrogateDiagTailX0RatChunk000Sub000Block140Part001
    + surrogateDiagTailX0RatChunk000Sub000Block140Part002
    + surrogateDiagTailX0RatChunk000Sub000Block140Part003
    + surrogateDiagTailX0RatChunk000Sub000Block140Part004
    + surrogateDiagTailX0RatChunk000Sub000Block140Part005
    + surrogateDiagTailX0RatChunk000Sub000Block140Part006
    + surrogateDiagTailX0RatChunk000Sub000Block140Part007
    + surrogateDiagTailX0RatChunk000Sub000Block140Part008
    + surrogateDiagTailX0RatChunk000Sub000Block140Part009
    + surrogateDiagTailX0RatChunk000Sub000Block140Part010
    + surrogateDiagTailX0RatChunk000Sub000Block140Part011
    + surrogateDiagTailX0RatChunk000Sub000Block140Part012
    + surrogateDiagTailX0RatChunk000Sub000Block140Part013
    + surrogateDiagTailX0RatChunk000Sub000Block140Part014
    + surrogateDiagTailX0RatChunk000Sub000Block140Part015
    + surrogateDiagTailX0RatChunk000Sub000Block140Part016
    + surrogateDiagTailX0RatChunk000Sub000Block140Part017
    + surrogateDiagTailX0RatChunk000Sub000Block140Part018
    + surrogateDiagTailX0RatChunk000Sub000Block140Part019
    + surrogateDiagTailX0RatChunk000Sub000Block140Part020
    + surrogateDiagTailX0RatChunk000Sub000Block140Part021
    + surrogateDiagTailX0RatChunk000Sub000Block140Part022
    + surrogateDiagTailX0RatChunk000Sub000Block140Part023
    + surrogateDiagTailX0RatChunk000Sub000Block140Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block140_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block140Head + surrogateDiagTailX0RatChunk000Sub000Block140Mid + surrogateDiagTailX0RatChunk000Sub000Block140Tail =
      surrogateDiagTailX0RatChunk000Sub000Block140 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block140Head surrogateDiagTailX0RatChunk000Sub000Block140Mid surrogateDiagTailX0RatChunk000Sub000Block140Tail surrogateDiagTailX0RatChunk000Sub000Block140
  ring

def SurrogateDiagonalTailChunk000Sub000Block140HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block140HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block140Head

def SurrogateDiagonalTailChunk000Sub000Block140MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block140MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block140Mid

def SurrogateDiagonalTailChunk000Sub000Block140TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block140TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block140Tail

theorem surrogateDiagonalTailChunk000Sub000Block140_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block140HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block140MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block140TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block140Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block140 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block140HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block140MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block140TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block140Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block140_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [50,60). -/

/-- Block 050 covers tail-support indices [11250,11275) and q from 18547 to 18589. -/

def TailChunk001Sub000Block050Part000SupportExplicit : Finset ℕ :=
  ([18547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part000 : ℚ :=
  (192386826877 : ℚ) / 2313197856885964800

def SurrogateDiagonalTailChunk001Sub000Block050Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18547
    = surrogateDiagTailX0RatChunk001Sub000Block050Part000

theorem surrogateDiagonalTailChunk001Sub000Block050Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part000] using hcert

def TailChunk001Sub000Block050Part001SupportExplicit : Finset ℕ :=
  ([18551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part001 : ℚ :=
  (18560380733125 : ℚ) / 214402549406634067968

def SurrogateDiagonalTailChunk001Sub000Block050Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18551
    = surrogateDiagTailX0RatChunk001Sub000Block050Part001

theorem surrogateDiagonalTailChunk001Sub000Block050Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part001] using hcert

def TailChunk001Sub000Block050Part002SupportExplicit : Finset ℕ :=
  ([18553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part002 : ℚ :=
  (5378340765625 : ℚ) / 74050809435636797952

def SurrogateDiagonalTailChunk001Sub000Block050Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18553
    = surrogateDiagTailX0RatChunk001Sub000Block050Part002

theorem surrogateDiagonalTailChunk001Sub000Block050Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part002] using hcert

def TailChunk001Sub000Block050Part003SupportExplicit : Finset ℕ :=
  ([18554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part003 : ℚ :=
  (1344730140625 : ℚ) / 4628175589727299872

def SurrogateDiagonalTailChunk001Sub000Block050Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18554
    = surrogateDiagTailX0RatChunk001Sub000Block050Part003

theorem surrogateDiagonalTailChunk001Sub000Block050Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part003] using hcert

def TailChunk001Sub000Block050Part004SupportExplicit : Finset ℕ :=
  ([18555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part004 : ℚ :=
  (557189697725 : ℚ) / 1991954636313329664

def SurrogateDiagonalTailChunk001Sub000Block050Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18555
    = surrogateDiagTailX0RatChunk001Sub000Block050Part004

theorem surrogateDiagonalTailChunk001Sub000Block050Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part004] using hcert

def TailChunk001Sub000Block050Part005SupportExplicit : Finset ℕ :=
  ([18557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part005 : ℚ :=
  (136594660921 : ℚ) / 1075169230848000000

def SurrogateDiagonalTailChunk001Sub000Block050Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18557
    = surrogateDiagTailX0RatChunk001Sub000Block050Part005

theorem surrogateDiagonalTailChunk001Sub000Block050Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part005] using hcert

def TailChunk001Sub000Block050Part006SupportExplicit : Finset ℕ :=
  ([18559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part006 : ℚ :=
  (10421089840625 : ℚ) / 137660370362376643584

def SurrogateDiagonalTailChunk001Sub000Block050Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18559
    = surrogateDiagTailX0RatChunk001Sub000Block050Part006

theorem surrogateDiagonalTailChunk001Sub000Block050Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part006] using hcert

def TailChunk001Sub000Block050Part007SupportExplicit : Finset ℕ :=
  ([18561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part007 : ℚ :=
  (184420403925 : ℚ) / 1007245889104254976

def SurrogateDiagonalTailChunk001Sub000Block050Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18561
    = surrogateDiagTailX0RatChunk001Sub000Block050Part007

theorem surrogateDiagonalTailChunk001Sub000Block050Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part007] using hcert

def TailChunk001Sub000Block050Part008SupportExplicit : Finset ℕ :=
  ([18562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part008 : ℚ :=
  (2153424025 : ℚ) / 7417862094323712

def SurrogateDiagonalTailChunk001Sub000Block050Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18562
    = surrogateDiagTailX0RatChunk001Sub000Block050Part008

theorem surrogateDiagonalTailChunk001Sub000Block050Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part008] using hcert

def TailChunk001Sub000Block050Part009SupportExplicit : Finset ℕ :=
  ([18563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part009 : ℚ :=
  (19534976092825 : ℚ) / 238185955494619250688

def SurrogateDiagonalTailChunk001Sub000Block050Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18563
    = surrogateDiagTailX0RatChunk001Sub000Block050Part009

theorem surrogateDiagonalTailChunk001Sub000Block050Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part009] using hcert

def TailChunk001Sub000Block050Part010SupportExplicit : Finset ℕ :=
  ([18565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part010 : ℚ :=
  (13825875488575 : ℚ) / 106090515990048964608

def SurrogateDiagonalTailChunk001Sub000Block050Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18565
    = surrogateDiagTailX0RatChunk001Sub000Block050Part010

theorem surrogateDiagonalTailChunk001Sub000Block050Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part010] using hcert

def TailChunk001Sub000Block050Part011SupportExplicit : Finset ℕ :=
  ([18566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part011 : ℚ :=
  (1346470140625 : ℚ) / 4640161794111074322

def SurrogateDiagonalTailChunk001Sub000Block050Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18566
    = surrogateDiagTailX0RatChunk001Sub000Block050Part011

theorem surrogateDiagonalTailChunk001Sub000Block050Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part011] using hcert

def TailChunk001Sub000Block050Part012SupportExplicit : Finset ℕ :=
  ([18569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part012 : ℚ :=
  (846050651 : ℚ) / 10792085366826270

def SurrogateDiagonalTailChunk001Sub000Block050Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18569
    = surrogateDiagTailX0RatChunk001Sub000Block050Part012

theorem surrogateDiagonalTailChunk001Sub000Block050Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part012] using hcert

def TailChunk001Sub000Block050Part013SupportExplicit : Finset ℕ :=
  ([18570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part013 : ℚ :=
  (1063568215625 : ℚ) / 746982988617498624

def SurrogateDiagonalTailChunk001Sub000Block050Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18570
    = surrogateDiagTailX0RatChunk001Sub000Block050Part013

theorem surrogateDiagonalTailChunk001Sub000Block050Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part013] using hcert

def TailChunk001Sub000Block050Part014SupportExplicit : Finset ℕ :=
  ([18573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part014 : ℚ :=
  (364458962101 : ℚ) / 2074014720000000000

def SurrogateDiagonalTailChunk001Sub000Block050Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18573
    = surrogateDiagTailX0RatChunk001Sub000Block050Part014

theorem surrogateDiagonalTailChunk001Sub000Block050Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part014] using hcert

def TailChunk001Sub000Block050Part015SupportExplicit : Finset ℕ :=
  ([18574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part015 : ℚ :=
  (1905460171 : ℚ) / 6076215000000000

def SurrogateDiagonalTailChunk001Sub000Block050Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18574
    = surrogateDiagTailX0RatChunk001Sub000Block050Part015

theorem surrogateDiagonalTailChunk001Sub000Block050Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part015] using hcert

def TailChunk001Sub000Block050Part016SupportExplicit : Finset ℕ :=
  ([18577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part016 : ℚ :=
  (9370214390675 : ℚ) / 107803950800251797504

def SurrogateDiagonalTailChunk001Sub000Block050Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18577
    = surrogateDiagTailX0RatChunk001Sub000Block050Part016

theorem surrogateDiagonalTailChunk001Sub000Block050Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part016] using hcert

def TailChunk001Sub000Block050Part017SupportExplicit : Finset ℕ :=
  ([18578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part017 : ℚ :=
  (238240493375 : ℚ) / 556587503833398336

def SurrogateDiagonalTailChunk001Sub000Block050Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18578
    = surrogateDiagTailX0RatChunk001Sub000Block050Part017

theorem surrogateDiagonalTailChunk001Sub000Block050Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part017] using hcert

def TailChunk001Sub000Block050Part018SupportExplicit : Finset ℕ :=
  ([18579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part018 : ℚ :=
  (32396321191 : ℚ) / 159643814115947520

def SurrogateDiagonalTailChunk001Sub000Block050Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18579
    = surrogateDiagTailX0RatChunk001Sub000Block050Part018

theorem surrogateDiagonalTailChunk001Sub000Block050Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part018] using hcert

def TailChunk001Sub000Block050Part019SupportExplicit : Finset ℕ :=
  ([18581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part019 : ℚ :=
  (6461415696625 : ℚ) / 77674074678572875776

def SurrogateDiagonalTailChunk001Sub000Block050Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18581
    = surrogateDiagTailX0RatChunk001Sub000Block050Part019

theorem surrogateDiagonalTailChunk001Sub000Block050Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part019] using hcert

def TailChunk001Sub000Block050Part020SupportExplicit : Finset ℕ :=
  ([18582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part020 : ℚ :=
  (2760638930125 : ℚ) / 2892656869256153088

def SurrogateDiagonalTailChunk001Sub000Block050Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18582
    = surrogateDiagTailX0RatChunk001Sub000Block050Part020

theorem surrogateDiagonalTailChunk001Sub000Block050Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part020] using hcert

def TailChunk001Sub000Block050Part021SupportExplicit : Finset ℕ :=
  ([18583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part021 : ℚ :=
  (5395748265625 : ℚ) / 74530955760787665522

def SurrogateDiagonalTailChunk001Sub000Block050Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18583
    = surrogateDiagTailX0RatChunk001Sub000Block050Part021

theorem surrogateDiagonalTailChunk001Sub000Block050Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part021] using hcert

def TailChunk001Sub000Block050Part022SupportExplicit : Finset ℕ :=
  ([18586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part022 : ℚ :=
  (1349372640625 : ℚ) / 4660190519932199712

def SurrogateDiagonalTailChunk001Sub000Block050Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18586
    = surrogateDiagTailX0RatChunk001Sub000Block050Part022

theorem surrogateDiagonalTailChunk001Sub000Block050Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part022] using hcert

def TailChunk001Sub000Block050Part023SupportExplicit : Finset ℕ :=
  ([18587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part023 : ℚ :=
  (5398071390625 : ℚ) / 74595151240066615602

def SurrogateDiagonalTailChunk001Sub000Block050Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18587
    = surrogateDiagTailX0RatChunk001Sub000Block050Part023

theorem surrogateDiagonalTailChunk001Sub000Block050Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part023] using hcert

def TailChunk001Sub000Block050Part024SupportExplicit : Finset ℕ :=
  ([18589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block050Part024 : ℚ :=
  (269789820777 : ℚ) / 3438092973663846400

def SurrogateDiagonalTailChunk001Sub000Block050Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18589
    = surrogateDiagTailX0RatChunk001Sub000Block050Part024

theorem surrogateDiagonalTailChunk001Sub000Block050Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block050Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block050Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block050Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block050Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block050Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block050HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block050Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block050Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block050Part000
    + surrogateDiagTailX0RatChunk001Sub000Block050Part001
    + surrogateDiagTailX0RatChunk001Sub000Block050Part002
    + surrogateDiagTailX0RatChunk001Sub000Block050Part003
    + surrogateDiagTailX0RatChunk001Sub000Block050Part004
    + surrogateDiagTailX0RatChunk001Sub000Block050Part005
    + surrogateDiagTailX0RatChunk001Sub000Block050Part006
    + surrogateDiagTailX0RatChunk001Sub000Block050Part007
    + surrogateDiagTailX0RatChunk001Sub000Block050Part008
    + surrogateDiagTailX0RatChunk001Sub000Block050Part009

def surrogateDiagonalTailChunk001Sub000Block050MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block050Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block050Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block050Part010
    + surrogateDiagTailX0RatChunk001Sub000Block050Part011
    + surrogateDiagTailX0RatChunk001Sub000Block050Part012
    + surrogateDiagTailX0RatChunk001Sub000Block050Part013
    + surrogateDiagTailX0RatChunk001Sub000Block050Part014
    + surrogateDiagTailX0RatChunk001Sub000Block050Part015
    + surrogateDiagTailX0RatChunk001Sub000Block050Part016
    + surrogateDiagTailX0RatChunk001Sub000Block050Part017
    + surrogateDiagTailX0RatChunk001Sub000Block050Part018
    + surrogateDiagTailX0RatChunk001Sub000Block050Part019

def surrogateDiagonalTailChunk001Sub000Block050TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block050Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block050Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block050Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block050Part020
    + surrogateDiagTailX0RatChunk001Sub000Block050Part021
    + surrogateDiagTailX0RatChunk001Sub000Block050Part022
    + surrogateDiagTailX0RatChunk001Sub000Block050Part023
    + surrogateDiagTailX0RatChunk001Sub000Block050Part024

def surrogateDiagonalTailChunk001Sub000Block050Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block050HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block050MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block050TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block050 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block050Part000
    + surrogateDiagTailX0RatChunk001Sub000Block050Part001
    + surrogateDiagTailX0RatChunk001Sub000Block050Part002
    + surrogateDiagTailX0RatChunk001Sub000Block050Part003
    + surrogateDiagTailX0RatChunk001Sub000Block050Part004
    + surrogateDiagTailX0RatChunk001Sub000Block050Part005
    + surrogateDiagTailX0RatChunk001Sub000Block050Part006
    + surrogateDiagTailX0RatChunk001Sub000Block050Part007
    + surrogateDiagTailX0RatChunk001Sub000Block050Part008
    + surrogateDiagTailX0RatChunk001Sub000Block050Part009
    + surrogateDiagTailX0RatChunk001Sub000Block050Part010
    + surrogateDiagTailX0RatChunk001Sub000Block050Part011
    + surrogateDiagTailX0RatChunk001Sub000Block050Part012
    + surrogateDiagTailX0RatChunk001Sub000Block050Part013
    + surrogateDiagTailX0RatChunk001Sub000Block050Part014
    + surrogateDiagTailX0RatChunk001Sub000Block050Part015
    + surrogateDiagTailX0RatChunk001Sub000Block050Part016
    + surrogateDiagTailX0RatChunk001Sub000Block050Part017
    + surrogateDiagTailX0RatChunk001Sub000Block050Part018
    + surrogateDiagTailX0RatChunk001Sub000Block050Part019
    + surrogateDiagTailX0RatChunk001Sub000Block050Part020
    + surrogateDiagTailX0RatChunk001Sub000Block050Part021
    + surrogateDiagTailX0RatChunk001Sub000Block050Part022
    + surrogateDiagTailX0RatChunk001Sub000Block050Part023
    + surrogateDiagTailX0RatChunk001Sub000Block050Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block050_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block050Head + surrogateDiagTailX0RatChunk001Sub000Block050Mid + surrogateDiagTailX0RatChunk001Sub000Block050Tail =
      surrogateDiagTailX0RatChunk001Sub000Block050 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block050Head surrogateDiagTailX0RatChunk001Sub000Block050Mid surrogateDiagTailX0RatChunk001Sub000Block050Tail surrogateDiagTailX0RatChunk001Sub000Block050
  ring

def SurrogateDiagonalTailChunk001Sub000Block050HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block050HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block050Head

def SurrogateDiagonalTailChunk001Sub000Block050MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block050MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block050Mid

def SurrogateDiagonalTailChunk001Sub000Block050TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block050TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block050Tail

theorem surrogateDiagonalTailChunk001Sub000Block050_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block050HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block050MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block050TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block050Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block050 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block050HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block050MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block050TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block050Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block050_eq_head_add_mid_add_tail

/-- Block 051 covers tail-support indices [11275,11300) and q from 18591 to 18631. -/

def TailChunk001Sub000Block051Part000SupportExplicit : Finset ℕ :=
  ([18591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part000 : ℚ :=
  (9598228380325 : ℚ) / 58964752218447464448

def SurrogateDiagonalTailChunk001Sub000Block051Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18591
    = surrogateDiagTailX0RatChunk001Sub000Block051Part000

theorem surrogateDiagonalTailChunk001Sub000Block051Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part000] using hcert

def TailChunk001Sub000Block051Part001SupportExplicit : Finset ℕ :=
  ([18593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part001 : ℚ :=
  (5401557015625 : ℚ) / 74691522203971878912

def SurrogateDiagonalTailChunk001Sub000Block051Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18593
    = surrogateDiagTailX0RatChunk001Sub000Block051Part001

theorem surrogateDiagonalTailChunk001Sub000Block051Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part001] using hcert

def TailChunk001Sub000Block051Part002SupportExplicit : Finset ℕ :=
  ([18595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part002 : ℚ :=
  (864048390625 : ℚ) / 7645121349669268608

def SurrogateDiagonalTailChunk001Sub000Block051Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18595
    = surrogateDiagTailX0RatChunk001Sub000Block051Part002

theorem surrogateDiagonalTailChunk001Sub000Block051Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part002] using hcert

def TailChunk001Sub000Block051Part003SupportExplicit : Finset ℕ :=
  ([18597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part003 : ℚ :=
  (9604425380125 : ℚ) / 59040921757651532928

def SurrogateDiagonalTailChunk001Sub000Block051Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18597
    = surrogateDiagTailX0RatChunk001Sub000Block051Part003

theorem surrogateDiagonalTailChunk001Sub000Block051Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part003] using hcert

def TailChunk001Sub000Block051Part004SupportExplicit : Finset ℕ :=
  ([18598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part004 : ℚ :=
  (4924640771125 : ℚ) / 14563889002232414208

def SurrogateDiagonalTailChunk001Sub000Block051Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18598
    = surrogateDiagTailX0RatChunk001Sub000Block051Part004

theorem surrogateDiagonalTailChunk001Sub000Block051Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part004] using hcert

def TailChunk001Sub000Block051Part005SupportExplicit : Finset ℕ :=
  ([18599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part005 : ℚ :=
  (16316079993025 : ℚ) / 161266493588250820608

def SurrogateDiagonalTailChunk001Sub000Block051Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18599
    = surrogateDiagTailX0RatChunk001Sub000Block051Part005

theorem surrogateDiagonalTailChunk001Sub000Block051Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part005] using hcert

def TailChunk001Sub000Block051Part006SupportExplicit : Finset ℕ :=
  ([18601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part006 : ℚ :=
  (20335314359 : ℚ) / 196769408860569600

def SurrogateDiagonalTailChunk001Sub000Block051Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18601
    = surrogateDiagTailX0RatChunk001Sub000Block051Part006

theorem surrogateDiagonalTailChunk001Sub000Block051Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part006] using hcert

def TailChunk001Sub000Block051Part007SupportExplicit : Finset ℕ :=
  ([18602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part007 : ℚ :=
  (209478145489 : ℚ) / 685886759922000000

def SurrogateDiagonalTailChunk001Sub000Block051Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18602
    = surrogateDiagTailX0RatChunk001Sub000Block051Part007

theorem surrogateDiagonalTailChunk001Sub000Block051Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part007] using hcert

def TailChunk001Sub000Block051Part008SupportExplicit : Finset ℕ :=
  ([18606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part008 : ℚ :=
  (1957142353975 : ℚ) / 1978977791407638528

def SurrogateDiagonalTailChunk001Sub000Block051Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18606
    = surrogateDiagTailX0RatChunk001Sub000Block051Part008

theorem surrogateDiagonalTailChunk001Sub000Block051Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part008] using hcert

def TailChunk001Sub000Block051Part009SupportExplicit : Finset ℕ :=
  ([18607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part009 : ℚ :=
  (19961612933125 : ℚ) / 249668082189468991488

def SurrogateDiagonalTailChunk001Sub000Block051Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18607
    = surrogateDiagTailX0RatChunk001Sub000Block051Part009

theorem surrogateDiagonalTailChunk001Sub000Block051Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part009] using hcert

def TailChunk001Sub000Block051Part010SupportExplicit : Finset ℕ :=
  ([18609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part010 : ℚ :=
  (9616825379725 : ℚ) / 59193482199510707328

def SurrogateDiagonalTailChunk001Sub000Block051Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18609
    = surrogateDiagTailX0RatChunk001Sub000Block051Part010

theorem surrogateDiagonalTailChunk001Sub000Block051Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part010] using hcert

def TailChunk001Sub000Block051Part011SupportExplicit : Finset ℕ :=
  ([18610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part011 : ℚ :=
  (155756229637 : ℚ) / 306463383716659200

def SurrogateDiagonalTailChunk001Sub000Block051Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18610
    = surrogateDiagTailX0RatChunk001Sub000Block051Part011

theorem surrogateDiagonalTailChunk001Sub000Block051Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part011] using hcert

def TailChunk001Sub000Block051Part012SupportExplicit : Finset ℕ :=
  ([18611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part012 : ℚ :=
  (20551111920475 : ℚ) / 266717634352123004928

def SurrogateDiagonalTailChunk001Sub000Block051Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18611
    = surrogateDiagTailX0RatChunk001Sub000Block051Part012

theorem surrogateDiagonalTailChunk001Sub000Block051Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part012] using hcert

def TailChunk001Sub000Block051Part013SupportExplicit : Finset ℕ :=
  ([18613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part013 : ℚ :=
  (1766448663625 : ℚ) / 17972531663241693312

def SurrogateDiagonalTailChunk001Sub000Block051Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18613
    = surrogateDiagTailX0RatChunk001Sub000Block051Part013

theorem surrogateDiagonalTailChunk001Sub000Block051Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part013] using hcert

def TailChunk001Sub000Block051Part014SupportExplicit : Finset ℕ :=
  ([18614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part014 : ℚ :=
  (41502766931 : ℚ) / 133595111810826240

def SurrogateDiagonalTailChunk001Sub000Block051Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18614
    = surrogateDiagTailX0RatChunk001Sub000Block051Part014

theorem surrogateDiagonalTailChunk001Sub000Block051Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part014] using hcert

def TailChunk001Sub000Block051Part015SupportExplicit : Finset ℕ :=
  ([18615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part015 : ℚ :=
  (5758137109675 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk001Sub000Block051Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18615
    = surrogateDiagTailX0RatChunk001Sub000Block051Part015

theorem surrogateDiagonalTailChunk001Sub000Block051Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part015] using hcert

def TailChunk001Sub000Block051Part016SupportExplicit : Finset ℕ :=
  ([18617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part016 : ℚ :=
  (5415510765625 : ℚ) / 75077940137615380992

def SurrogateDiagonalTailChunk001Sub000Block051Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18617
    = surrogateDiagTailX0RatChunk001Sub000Block051Part016

theorem surrogateDiagonalTailChunk001Sub000Block051Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part016] using hcert

def TailChunk001Sub000Block051Part017SupportExplicit : Finset ℕ :=
  ([18618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part017 : ℚ :=
  (1141678509575 : ℚ) / 1552288472266850304

def SurrogateDiagonalTailChunk001Sub000Block051Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18618
    = surrogateDiagTailX0RatChunk001Sub000Block051Part017

theorem surrogateDiagonalTailChunk001Sub000Block051Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part017] using hcert

def TailChunk001Sub000Block051Part018SupportExplicit : Finset ℕ :=
  ([18619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part018 : ℚ :=
  (80932010725 : ℚ) / 1058568685121783808

def SurrogateDiagonalTailChunk001Sub000Block051Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18619
    = surrogateDiagTailX0RatChunk001Sub000Block051Part018

theorem surrogateDiagonalTailChunk001Sub000Block051Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part018] using hcert

def TailChunk001Sub000Block051Part019SupportExplicit : Finset ℕ :=
  ([18622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part019 : ℚ :=
  (2167368025 : ℚ) / 7514248860472242

def SurrogateDiagonalTailChunk001Sub000Block051Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18622
    = surrogateDiagTailX0RatChunk001Sub000Block051Part019

theorem surrogateDiagonalTailChunk001Sub000Block051Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part019] using hcert

def TailChunk001Sub000Block051Part020SupportExplicit : Finset ℕ :=
  ([18623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part020 : ℚ :=
  (182552386309 : ℚ) / 2049407370138124800

def SurrogateDiagonalTailChunk001Sub000Block051Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18623
    = surrogateDiagTailX0RatChunk001Sub000Block051Part020

theorem surrogateDiagonalTailChunk001Sub000Block051Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part020] using hcert

def TailChunk001Sub000Block051Part021SupportExplicit : Finset ℕ :=
  ([18626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part021 : ℚ :=
  (43369089175 : ℚ) / 142211126407413888

def SurrogateDiagonalTailChunk001Sub000Block051Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18626
    = surrogateDiagTailX0RatChunk001Sub000Block051Part021

theorem surrogateDiagonalTailChunk001Sub000Block051Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part021] using hcert

def TailChunk001Sub000Block051Part022SupportExplicit : Finset ℕ :=
  ([18627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part022 : ℚ :=
  (7460766031225 : ℚ) / 31951167401318565888

def SurrogateDiagonalTailChunk001Sub000Block051Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18627
    = surrogateDiagTailX0RatChunk001Sub000Block051Part022

theorem surrogateDiagonalTailChunk001Sub000Block051Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part022] using hcert

def TailChunk001Sub000Block051Part023SupportExplicit : Finset ℕ :=
  ([18629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part023 : ℚ :=
  (9422771607425 : ℚ) / 109016922845390045184

def SurrogateDiagonalTailChunk001Sub000Block051Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18629
    = surrogateDiagTailX0RatChunk001Sub000Block051Part023

theorem surrogateDiagonalTailChunk001Sub000Block051Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part023] using hcert

def TailChunk001Sub000Block051Part024SupportExplicit : Finset ℕ :=
  ([18631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block051Part024 : ℚ :=
  (51103003219 : ℚ) / 656231220000000000

def SurrogateDiagonalTailChunk001Sub000Block051Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18631
    = surrogateDiagTailX0RatChunk001Sub000Block051Part024

theorem surrogateDiagonalTailChunk001Sub000Block051Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block051Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block051Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block051Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block051Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block051Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block051HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block051Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block051Part000
    + surrogateDiagTailX0RatChunk001Sub000Block051Part001
    + surrogateDiagTailX0RatChunk001Sub000Block051Part002
    + surrogateDiagTailX0RatChunk001Sub000Block051Part003
    + surrogateDiagTailX0RatChunk001Sub000Block051Part004
    + surrogateDiagTailX0RatChunk001Sub000Block051Part005
    + surrogateDiagTailX0RatChunk001Sub000Block051Part006
    + surrogateDiagTailX0RatChunk001Sub000Block051Part007
    + surrogateDiagTailX0RatChunk001Sub000Block051Part008
    + surrogateDiagTailX0RatChunk001Sub000Block051Part009

def surrogateDiagonalTailChunk001Sub000Block051MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block051Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block051Part010
    + surrogateDiagTailX0RatChunk001Sub000Block051Part011
    + surrogateDiagTailX0RatChunk001Sub000Block051Part012
    + surrogateDiagTailX0RatChunk001Sub000Block051Part013
    + surrogateDiagTailX0RatChunk001Sub000Block051Part014
    + surrogateDiagTailX0RatChunk001Sub000Block051Part015
    + surrogateDiagTailX0RatChunk001Sub000Block051Part016
    + surrogateDiagTailX0RatChunk001Sub000Block051Part017
    + surrogateDiagTailX0RatChunk001Sub000Block051Part018
    + surrogateDiagTailX0RatChunk001Sub000Block051Part019

def surrogateDiagonalTailChunk001Sub000Block051TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block051Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block051Part020
    + surrogateDiagTailX0RatChunk001Sub000Block051Part021
    + surrogateDiagTailX0RatChunk001Sub000Block051Part022
    + surrogateDiagTailX0RatChunk001Sub000Block051Part023
    + surrogateDiagTailX0RatChunk001Sub000Block051Part024

def surrogateDiagonalTailChunk001Sub000Block051Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block051HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block051MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block051TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block051 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block051Part000
    + surrogateDiagTailX0RatChunk001Sub000Block051Part001
    + surrogateDiagTailX0RatChunk001Sub000Block051Part002
    + surrogateDiagTailX0RatChunk001Sub000Block051Part003
    + surrogateDiagTailX0RatChunk001Sub000Block051Part004
    + surrogateDiagTailX0RatChunk001Sub000Block051Part005
    + surrogateDiagTailX0RatChunk001Sub000Block051Part006
    + surrogateDiagTailX0RatChunk001Sub000Block051Part007
    + surrogateDiagTailX0RatChunk001Sub000Block051Part008
    + surrogateDiagTailX0RatChunk001Sub000Block051Part009
    + surrogateDiagTailX0RatChunk001Sub000Block051Part010
    + surrogateDiagTailX0RatChunk001Sub000Block051Part011
    + surrogateDiagTailX0RatChunk001Sub000Block051Part012
    + surrogateDiagTailX0RatChunk001Sub000Block051Part013
    + surrogateDiagTailX0RatChunk001Sub000Block051Part014
    + surrogateDiagTailX0RatChunk001Sub000Block051Part015
    + surrogateDiagTailX0RatChunk001Sub000Block051Part016
    + surrogateDiagTailX0RatChunk001Sub000Block051Part017
    + surrogateDiagTailX0RatChunk001Sub000Block051Part018
    + surrogateDiagTailX0RatChunk001Sub000Block051Part019
    + surrogateDiagTailX0RatChunk001Sub000Block051Part020
    + surrogateDiagTailX0RatChunk001Sub000Block051Part021
    + surrogateDiagTailX0RatChunk001Sub000Block051Part022
    + surrogateDiagTailX0RatChunk001Sub000Block051Part023
    + surrogateDiagTailX0RatChunk001Sub000Block051Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block051_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block051Head + surrogateDiagTailX0RatChunk001Sub000Block051Mid + surrogateDiagTailX0RatChunk001Sub000Block051Tail =
      surrogateDiagTailX0RatChunk001Sub000Block051 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block051Head surrogateDiagTailX0RatChunk001Sub000Block051Mid surrogateDiagTailX0RatChunk001Sub000Block051Tail surrogateDiagTailX0RatChunk001Sub000Block051
  ring

def SurrogateDiagonalTailChunk001Sub000Block051HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block051HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block051Head

def SurrogateDiagonalTailChunk001Sub000Block051MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block051MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block051Mid

def SurrogateDiagonalTailChunk001Sub000Block051TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block051TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block051Tail

theorem surrogateDiagonalTailChunk001Sub000Block051_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block051HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block051MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block051TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block051Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block051 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block051HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block051MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block051TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block051Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block051_eq_head_add_mid_add_tail

/-- Block 052 covers tail-support indices [11300,11325) and q from 18633 to 18673. -/

def TailChunk001Sub000Block052Part000SupportExplicit : Finset ℕ :=
  ([18633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part000 : ℚ :=
  (385665975157 : ℚ) / 2379979594834819200

def SurrogateDiagonalTailChunk001Sub000Block052Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18633
    = surrogateDiagTailX0RatChunk001Sub000Block052Part000

theorem surrogateDiagonalTailChunk001Sub000Block052Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part000] using hcert

def TailChunk001Sub000Block052Part001SupportExplicit : Finset ℕ :=
  ([18635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part001 : ℚ :=
  (289256796875 : ℚ) / 2570377962421604736

def SurrogateDiagonalTailChunk001Sub000Block052Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18635
    = surrogateDiagTailX0RatChunk001Sub000Block052Part001

theorem surrogateDiagonalTailChunk001Sub000Block052Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part001] using hcert

def TailChunk001Sub000Block052Part002SupportExplicit : Finset ℕ :=
  ([18637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part002 : ℚ :=
  (5427152640625 : ℚ) / 75401098780468990752

def SurrogateDiagonalTailChunk001Sub000Block052Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18637
    = surrogateDiagTailX0RatChunk001Sub000Block052Part002

theorem surrogateDiagonalTailChunk001Sub000Block052Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part002] using hcert

def TailChunk001Sub000Block052Part003SupportExplicit : Finset ℕ :=
  ([18638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part003 : ℚ :=
  (1356933765625 : ℚ) / 4712568673779311922

def SurrogateDiagonalTailChunk001Sub000Block052Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18638
    = surrogateDiagTailX0RatChunk001Sub000Block052Part003

theorem surrogateDiagonalTailChunk001Sub000Block052Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part003] using hcert

def TailChunk001Sub000Block052Part004SupportExplicit : Finset ℕ :=
  ([18641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part004 : ℚ :=
  (16389872023225 : ℚ) / 162728666274626483328

def SurrogateDiagonalTailChunk001Sub000Block052Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18641
    = surrogateDiagTailX0RatChunk001Sub000Block052Part004

theorem surrogateDiagonalTailChunk001Sub000Block052Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part004] using hcert

def TailChunk001Sub000Block052Part005SupportExplicit : Finset ℕ :=
  ([18642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part005 : ℚ :=
  (191736631175 : ℚ) / 190130424691802112

def SurrogateDiagonalTailChunk001Sub000Block052Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18642
    = surrogateDiagTailX0RatChunk001Sub000Block052Part005

theorem surrogateDiagonalTailChunk001Sub000Block052Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part005] using hcert

def TailChunk001Sub000Block052Part006SupportExplicit : Finset ℕ :=
  ([18643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part006 : ℚ :=
  (18804935521 : ℚ) / 252560276239656960

def SurrogateDiagonalTailChunk001Sub000Block052Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18643
    = surrogateDiagTailX0RatChunk001Sub000Block052Part006

theorem surrogateDiagonalTailChunk001Sub000Block052Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part006] using hcert

def TailChunk001Sub000Block052Part007SupportExplicit : Finset ℕ :=
  ([18645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part007 : ℚ :=
  (220230250867 : ℚ) / 644642432561971200

def SurrogateDiagonalTailChunk001Sub000Block052Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18645
    = surrogateDiagTailX0RatChunk001Sub000Block052Part007

theorem surrogateDiagonalTailChunk001Sub000Block052Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part007] using hcert

def TailChunk001Sub000Block052Part008SupportExplicit : Finset ℕ :=
  ([18646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part008 : ℚ :=
  (1358098890625 : ℚ) / 4720665868947322482

def SurrogateDiagonalTailChunk001Sub000Block052Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18646
    = surrogateDiagTailX0RatChunk001Sub000Block052Part008

theorem surrogateDiagonalTailChunk001Sub000Block052Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part008] using hcert

def TailChunk001Sub000Block052Part009SupportExplicit : Finset ℕ :=
  ([18647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part009 : ℚ :=
  (20386831604425 : ℚ) / 261095325495883941888

def SurrogateDiagonalTailChunk001Sub000Block052Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18647
    = surrogateDiagTailX0RatChunk001Sub000Block052Part009

theorem surrogateDiagonalTailChunk001Sub000Block052Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part009] using hcert

def TailChunk001Sub000Block052Part010SupportExplicit : Finset ℕ :=
  ([18649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part010 : ℚ :=
  (6508826587425 : ℚ) / 78818424839194279936

def SurrogateDiagonalTailChunk001Sub000Block052Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18649
    = surrogateDiagTailX0RatChunk001Sub000Block052Part010

theorem surrogateDiagonalTailChunk001Sub000Block052Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part010] using hcert

def TailChunk001Sub000Block052Part011SupportExplicit : Finset ℕ :=
  ([18651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part011 : ℚ :=
  (9660288378325 : ℚ) / 59729773065353330688

def SurrogateDiagonalTailChunk001Sub000Block052Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18651
    = surrogateDiagTailX0RatChunk001Sub000Block052Part011

theorem surrogateDiagonalTailChunk001Sub000Block052Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part011] using hcert

def TailChunk001Sub000Block052Part012SupportExplicit : Finset ℕ :=
  ([18653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part012 : ℚ :=
  (9906430247 : ℚ) / 124518141544579200

def SurrogateDiagonalTailChunk001Sub000Block052Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18653
    = surrogateDiagTailX0RatChunk001Sub000Block052Part012

theorem surrogateDiagonalTailChunk001Sub000Block052Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part012] using hcert

def TailChunk001Sub000Block052Part013SupportExplicit : Finset ℕ :=
  ([18654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part013 : ℚ :=
  (1509876421475 : ℚ) / 1866555408292291584

def SurrogateDiagonalTailChunk001Sub000Block052Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18654
    = surrogateDiagTailX0RatChunk001Sub000Block052Part013

theorem surrogateDiagonalTailChunk001Sub000Block052Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part013] using hcert

def TailChunk001Sub000Block052Part014SupportExplicit : Finset ℕ :=
  ([18655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part014 : ℚ :=
  (1238122421 : ℚ) / 6116518291046400

def SurrogateDiagonalTailChunk001Sub000Block052Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18655
    = surrogateDiagTailX0RatChunk001Sub000Block052Part014

theorem surrogateDiagonalTailChunk001Sub000Block052Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part014] using hcert

def TailChunk001Sub000Block052Part015SupportExplicit : Finset ℕ :=
  ([18658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part015 : ℚ :=
  (100068766247 : ℚ) / 302643391462977600

def SurrogateDiagonalTailChunk001Sub000Block052Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18658
    = surrogateDiagTailX0RatChunk001Sub000Block052Part015

theorem surrogateDiagonalTailChunk001Sub000Block052Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part015] using hcert

def TailChunk001Sub000Block052Part016SupportExplicit : Finset ℕ :=
  ([18659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part016 : ℚ :=
  (20872609715275 : ℚ) / 275320740724753287168

def SurrogateDiagonalTailChunk001Sub000Block052Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18659
    = surrogateDiagTailX0RatChunk001Sub000Block052Part016

theorem surrogateDiagonalTailChunk001Sub000Block052Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part016] using hcert

def TailChunk001Sub000Block052Part017SupportExplicit : Finset ℕ :=
  ([18661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part017 : ℚ :=
  (8705823025 : ℚ) / 121264423894531872

def SurrogateDiagonalTailChunk001Sub000Block052Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18661
    = surrogateDiagTailX0RatChunk001Sub000Block052Part017

theorem surrogateDiagonalTailChunk001Sub000Block052Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part017] using hcert

def TailChunk001Sub000Block052Part018SupportExplicit : Finset ℕ :=
  ([18662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part018 : ℚ :=
  (5770916549 : ℚ) / 12100693702809600

def SurrogateDiagonalTailChunk001Sub000Block052Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18662
    = surrogateDiagTailX0RatChunk001Sub000Block052Part018

theorem surrogateDiagonalTailChunk001Sub000Block052Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part018] using hcert

def TailChunk001Sub000Block052Part019SupportExplicit : Finset ℕ :=
  ([18663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part019 : ℚ :=
  (386908975117 : ℚ) / 2395346644830259200

def SurrogateDiagonalTailChunk001Sub000Block052Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18663
    = surrogateDiagTailX0RatChunk001Sub000Block052Part019

theorem surrogateDiagonalTailChunk001Sub000Block052Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part019] using hcert

def TailChunk001Sub000Block052Part020SupportExplicit : Finset ℕ :=
  ([18665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part020 : ℚ :=
  (14800956249775 : ℚ) / 124174770068000636928

def SurrogateDiagonalTailChunk001Sub000Block052Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18665
    = surrogateDiagTailX0RatChunk001Sub000Block052Part020

theorem surrogateDiagonalTailChunk001Sub000Block052Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part020] using hcert

def TailChunk001Sub000Block052Part021SupportExplicit : Finset ℕ :=
  ([18667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part021 : ℚ :=
  (61138796883 : ℚ) / 689618646571417600

def SurrogateDiagonalTailChunk001Sub000Block052Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18667
    = surrogateDiagTailX0RatChunk001Sub000Block052Part021

theorem surrogateDiagonalTailChunk001Sub000Block052Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part021] using hcert

def TailChunk001Sub000Block052Part022SupportExplicit : Finset ℕ :=
  ([18670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part022 : ℚ :=
  (3919060153825 : ℚ) / 7760923129250039808

def SurrogateDiagonalTailChunk001Sub000Block052Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18670
    = surrogateDiagTailX0RatChunk001Sub000Block052Part022

theorem surrogateDiagonalTailChunk001Sub000Block052Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part022] using hcert

def TailChunk001Sub000Block052Part023SupportExplicit : Finset ℕ :=
  ([18671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part023 : ℚ :=
  (8715156025 : ℚ) / 121524578102819442

def SurrogateDiagonalTailChunk001Sub000Block052Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18671
    = surrogateDiagTailX0RatChunk001Sub000Block052Part023

theorem surrogateDiagonalTailChunk001Sub000Block052Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part023] using hcert

def TailChunk001Sub000Block052Part024SupportExplicit : Finset ℕ :=
  ([18673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block052Part024 : ℚ :=
  (140818423113 : ℚ) / 1885961944488171200

def SurrogateDiagonalTailChunk001Sub000Block052Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18673
    = surrogateDiagTailX0RatChunk001Sub000Block052Part024

theorem surrogateDiagonalTailChunk001Sub000Block052Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block052Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block052Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block052Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block052Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block052Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block052HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block052Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block052Part000
    + surrogateDiagTailX0RatChunk001Sub000Block052Part001
    + surrogateDiagTailX0RatChunk001Sub000Block052Part002
    + surrogateDiagTailX0RatChunk001Sub000Block052Part003
    + surrogateDiagTailX0RatChunk001Sub000Block052Part004
    + surrogateDiagTailX0RatChunk001Sub000Block052Part005
    + surrogateDiagTailX0RatChunk001Sub000Block052Part006
    + surrogateDiagTailX0RatChunk001Sub000Block052Part007
    + surrogateDiagTailX0RatChunk001Sub000Block052Part008
    + surrogateDiagTailX0RatChunk001Sub000Block052Part009

def surrogateDiagonalTailChunk001Sub000Block052MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block052Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block052Part010
    + surrogateDiagTailX0RatChunk001Sub000Block052Part011
    + surrogateDiagTailX0RatChunk001Sub000Block052Part012
    + surrogateDiagTailX0RatChunk001Sub000Block052Part013
    + surrogateDiagTailX0RatChunk001Sub000Block052Part014
    + surrogateDiagTailX0RatChunk001Sub000Block052Part015
    + surrogateDiagTailX0RatChunk001Sub000Block052Part016
    + surrogateDiagTailX0RatChunk001Sub000Block052Part017
    + surrogateDiagTailX0RatChunk001Sub000Block052Part018
    + surrogateDiagTailX0RatChunk001Sub000Block052Part019

def surrogateDiagonalTailChunk001Sub000Block052TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block052Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block052Part020
    + surrogateDiagTailX0RatChunk001Sub000Block052Part021
    + surrogateDiagTailX0RatChunk001Sub000Block052Part022
    + surrogateDiagTailX0RatChunk001Sub000Block052Part023
    + surrogateDiagTailX0RatChunk001Sub000Block052Part024

def surrogateDiagonalTailChunk001Sub000Block052Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block052HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block052MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block052TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block052 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block052Part000
    + surrogateDiagTailX0RatChunk001Sub000Block052Part001
    + surrogateDiagTailX0RatChunk001Sub000Block052Part002
    + surrogateDiagTailX0RatChunk001Sub000Block052Part003
    + surrogateDiagTailX0RatChunk001Sub000Block052Part004
    + surrogateDiagTailX0RatChunk001Sub000Block052Part005
    + surrogateDiagTailX0RatChunk001Sub000Block052Part006
    + surrogateDiagTailX0RatChunk001Sub000Block052Part007
    + surrogateDiagTailX0RatChunk001Sub000Block052Part008
    + surrogateDiagTailX0RatChunk001Sub000Block052Part009
    + surrogateDiagTailX0RatChunk001Sub000Block052Part010
    + surrogateDiagTailX0RatChunk001Sub000Block052Part011
    + surrogateDiagTailX0RatChunk001Sub000Block052Part012
    + surrogateDiagTailX0RatChunk001Sub000Block052Part013
    + surrogateDiagTailX0RatChunk001Sub000Block052Part014
    + surrogateDiagTailX0RatChunk001Sub000Block052Part015
    + surrogateDiagTailX0RatChunk001Sub000Block052Part016
    + surrogateDiagTailX0RatChunk001Sub000Block052Part017
    + surrogateDiagTailX0RatChunk001Sub000Block052Part018
    + surrogateDiagTailX0RatChunk001Sub000Block052Part019
    + surrogateDiagTailX0RatChunk001Sub000Block052Part020
    + surrogateDiagTailX0RatChunk001Sub000Block052Part021
    + surrogateDiagTailX0RatChunk001Sub000Block052Part022
    + surrogateDiagTailX0RatChunk001Sub000Block052Part023
    + surrogateDiagTailX0RatChunk001Sub000Block052Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block052_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block052Head + surrogateDiagTailX0RatChunk001Sub000Block052Mid + surrogateDiagTailX0RatChunk001Sub000Block052Tail =
      surrogateDiagTailX0RatChunk001Sub000Block052 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block052Head surrogateDiagTailX0RatChunk001Sub000Block052Mid surrogateDiagTailX0RatChunk001Sub000Block052Tail surrogateDiagTailX0RatChunk001Sub000Block052
  ring

def SurrogateDiagonalTailChunk001Sub000Block052HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block052HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block052Head

def SurrogateDiagonalTailChunk001Sub000Block052MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block052MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block052Mid

def SurrogateDiagonalTailChunk001Sub000Block052TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block052TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block052Tail

theorem surrogateDiagonalTailChunk001Sub000Block052_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block052HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block052MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block052TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block052Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block052 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block052HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block052MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block052TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block052Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block052_eq_head_add_mid_add_tail

/-- Block 053 covers tail-support indices [11325,11350) and q from 18674 to 18710. -/

def TailChunk001Sub000Block053Part000SupportExplicit : Finset ℕ :=
  ([18674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part000 : ℚ :=
  (1362180765625 : ℚ) / 4749088247425700352

def SurrogateDiagonalTailChunk001Sub000Block053Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18674
    = surrogateDiagTailX0RatChunk001Sub000Block053Part000

theorem surrogateDiagonalTailChunk001Sub000Block053Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part000] using hcert

def TailChunk001Sub000Block053Part001SupportExplicit : Finset ℕ :=
  ([18677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part001 : ℚ :=
  (19775829439225 : ℚ) / 244097218391323356288

def SurrogateDiagonalTailChunk001Sub000Block053Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18677
    = surrogateDiagTailX0RatChunk001Sub000Block053Part001

theorem surrogateDiagonalTailChunk001Sub000Block053Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part001] using hcert

def TailChunk001Sub000Block053Part002SupportExplicit : Finset ℕ :=
  ([18678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part002 : ℚ :=
  (235185805 : ℚ) / 224900671620096

def SurrogateDiagonalTailChunk001Sub000Block053Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18678
    = surrogateDiagTailX0RatChunk001Sub000Block053Part002

theorem surrogateDiagonalTailChunk001Sub000Block053Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part002] using hcert

def TailChunk001Sub000Block053Part003SupportExplicit : Finset ℕ :=
  ([18679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part003 : ℚ :=
  (5451641265625 : ℚ) / 76083126669819850482

def SurrogateDiagonalTailChunk001Sub000Block053Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18679
    = surrogateDiagTailX0RatChunk001Sub000Block053Part003

theorem surrogateDiagonalTailChunk001Sub000Block053Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part003] using hcert

def TailChunk001Sub000Block053Part004SupportExplicit : Finset ℕ :=
  ([18681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part004 : ℚ :=
  (2834704688375 : ℚ) / 14436508053284683776

def SurrogateDiagonalTailChunk001Sub000Block053Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18681
    = surrogateDiagTailX0RatChunk001Sub000Block053Part004

theorem surrogateDiagonalTailChunk001Sub000Block053Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part004] using hcert

def TailChunk001Sub000Block053Part005SupportExplicit : Finset ℕ :=
  ([18682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part005 : ℚ :=
  (2181357025 : ℚ) / 7611571917341472

def SurrogateDiagonalTailChunk001Sub000Block053Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18682
    = surrogateDiagTailX0RatChunk001Sub000Block053Part005

theorem surrogateDiagonalTailChunk001Sub000Block053Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part005] using hcert

def TailChunk001Sub000Block053Part006SupportExplicit : Finset ℕ :=
  ([18683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part006 : ℚ :=
  (1836966969125 : ℚ) / 15722449101951860736

def SurrogateDiagonalTailChunk001Sub000Block053Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18683
    = surrogateDiagTailX0RatChunk001Sub000Block053Part006

theorem surrogateDiagonalTailChunk001Sub000Block053Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part006] using hcert

def TailChunk001Sub000Block053Part007SupportExplicit : Finset ℕ :=
  ([18685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part007 : ℚ :=
  (278583143969 : ℚ) / 2150338461696000000

def SurrogateDiagonalTailChunk001Sub000Block053Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18685
    = surrogateDiagTailX0RatChunk001Sub000Block053Part007

theorem surrogateDiagonalTailChunk001Sub000Block053Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part007] using hcert

def TailChunk001Sub000Block053Part008SupportExplicit : Finset ℕ :=
  ([18686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part008 : ℚ :=
  (1363932015625 : ℚ) / 4761308474621478162

def SurrogateDiagonalTailChunk001Sub000Block053Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18686
    = surrogateDiagTailX0RatChunk001Sub000Block053Part008

theorem surrogateDiagonalTailChunk001Sub000Block053Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part008] using hcert

def TailChunk001Sub000Block053Part009SupportExplicit : Finset ℕ :=
  ([18687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part009 : ℚ :=
  (9697620377125 : ℚ) / 60192344172992514048

def SurrogateDiagonalTailChunk001Sub000Block053Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18687
    = surrogateDiagTailX0RatChunk001Sub000Block053Part009

theorem surrogateDiagonalTailChunk001Sub000Block053Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part009] using hcert

def TailChunk001Sub000Block053Part010SupportExplicit : Finset ℕ :=
  ([18689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part010 : ℚ :=
  (45962289469 : ℚ) / 519657992417320200

def SurrogateDiagonalTailChunk001Sub000Block053Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18689
    = surrogateDiagTailX0RatChunk001Sub000Block053Part010

theorem surrogateDiagonalTailChunk001Sub000Block053Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part010] using hcert

def TailChunk001Sub000Block053Part011SupportExplicit : Finset ℕ :=
  ([18690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part011 : ℚ :=
  (1795756114375 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk001Sub000Block053Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18690
    = surrogateDiagTailX0RatChunk001Sub000Block053Part011

theorem surrogateDiagonalTailChunk001Sub000Block053Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part011] using hcert

def TailChunk001Sub000Block053Part012SupportExplicit : Finset ℕ :=
  ([18691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part012 : ℚ :=
  (8733837025 : ℚ) / 122046142066753842

def SurrogateDiagonalTailChunk001Sub000Block053Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18691
    = surrogateDiagTailX0RatChunk001Sub000Block053Part012

theorem surrogateDiagonalTailChunk001Sub000Block053Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part012] using hcert

def TailChunk001Sub000Block053Part013SupportExplicit : Finset ℕ :=
  ([18694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part013 : ℚ :=
  (4837516780075 : ℚ) / 13780012770283603968

def SurrogateDiagonalTailChunk001Sub000Block053Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18694
    = surrogateDiagTailX0RatChunk001Sub000Block053Part013

theorem surrogateDiagonalTailChunk001Sub000Block053Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part013] using hcert

def TailChunk001Sub000Block053Part014SupportExplicit : Finset ℕ :=
  ([18695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part014 : ℚ :=
  (14848581982225 : ℚ) / 124975249476355934208

def SurrogateDiagonalTailChunk001Sub000Block053Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18695
    = surrogateDiagTailX0RatChunk001Sub000Block053Part014

theorem surrogateDiagonalTailChunk001Sub000Block053Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part014] using hcert

def TailChunk001Sub000Block053Part015SupportExplicit : Finset ℕ :=
  ([18697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part015 : ℚ :=
  (131908163309 : ℚ) / 1317549355422848640

def SurrogateDiagonalTailChunk001Sub000Block053Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18697
    = surrogateDiagTailX0RatChunk001Sub000Block053Part015

theorem surrogateDiagonalTailChunk001Sub000Block053Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part015] using hcert

def TailChunk001Sub000Block053Part016SupportExplicit : Finset ℕ :=
  ([18698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part016 : ℚ :=
  (1365684390625 : ℚ) / 4773552270231896352

def SurrogateDiagonalTailChunk001Sub000Block053Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18698
    = surrogateDiagTailX0RatChunk001Sub000Block053Part016

theorem surrogateDiagonalTailChunk001Sub000Block053Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part016] using hcert

def TailChunk001Sub000Block053Part017SupportExplicit : Finset ℕ :=
  ([18699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part017 : ℚ :=
  (19955821507 : ℚ) / 110682792484070400

def SurrogateDiagonalTailChunk001Sub000Block053Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18699
    = surrogateDiagTailX0RatChunk001Sub000Block053Part017

theorem surrogateDiagonalTailChunk001Sub000Block053Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part017] using hcert

def TailChunk001Sub000Block053Part018SupportExplicit : Finset ℕ :=
  ([18701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part018 : ℚ :=
  (349727401 : ℚ) / 4892302108768800

def SurrogateDiagonalTailChunk001Sub000Block053Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18701
    = surrogateDiagTailX0RatChunk001Sub000Block053Part018

theorem surrogateDiagonalTailChunk001Sub000Block053Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part018] using hcert

def TailChunk001Sub000Block053Part019SupportExplicit : Finset ℕ :=
  ([18703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part019 : ℚ :=
  (3518034965025 : ℚ) / 47025769762489945088

def SurrogateDiagonalTailChunk001Sub000Block053Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18703
    = surrogateDiagTailX0RatChunk001Sub000Block053Part019

theorem surrogateDiagonalTailChunk001Sub000Block053Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part019] using hcert

def TailChunk001Sub000Block053Part020SupportExplicit : Finset ℕ :=
  ([18705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part020 : ℚ :=
  (771027631525 : ℚ) / 19589172644856987648

def SurrogateDiagonalTailChunk001Sub000Block053Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18705
    = surrogateDiagTailX0RatChunk001Sub000Block053Part020

theorem surrogateDiagonalTailChunk001Sub000Block053Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part020] using hcert

def TailChunk001Sub000Block053Part021SupportExplicit : Finset ℕ :=
  ([18706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part021 : ℚ :=
  (25095738875 : ℚ) / 5735848765099026816

def SurrogateDiagonalTailChunk001Sub000Block053Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18706
    = surrogateDiagTailX0RatChunk001Sub000Block053Part021

theorem surrogateDiagonalTailChunk001Sub000Block053Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part021] using hcert

def TailChunk001Sub000Block053Part022SupportExplicit : Finset ℕ :=
  ([18707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part022 : ℚ :=
  (97829742325 : ℚ) / 55427768693105766912

def SurrogateDiagonalTailChunk001Sub000Block053Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18707
    = surrogateDiagTailX0RatChunk001Sub000Block053Part022

theorem surrogateDiagonalTailChunk001Sub000Block053Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part022] using hcert

def TailChunk001Sub000Block053Part023SupportExplicit : Finset ℕ :=
  ([18709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part023 : ℚ :=
  (62246099075 : ℚ) / 140339812407667851264

def SurrogateDiagonalTailChunk001Sub000Block053Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18709
    = surrogateDiagTailX0RatChunk001Sub000Block053Part023

theorem surrogateDiagonalTailChunk001Sub000Block053Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part023] using hcert

def TailChunk001Sub000Block053Part024SupportExplicit : Finset ℕ :=
  ([18710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block053Part024 : ℚ :=
  (17531025649 : ℚ) / 313107334961203200

def SurrogateDiagonalTailChunk001Sub000Block053Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18710
    = surrogateDiagTailX0RatChunk001Sub000Block053Part024

theorem surrogateDiagonalTailChunk001Sub000Block053Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block053Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block053Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block053Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block053Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block053Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block053HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block053Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block053Part000
    + surrogateDiagTailX0RatChunk001Sub000Block053Part001
    + surrogateDiagTailX0RatChunk001Sub000Block053Part002
    + surrogateDiagTailX0RatChunk001Sub000Block053Part003
    + surrogateDiagTailX0RatChunk001Sub000Block053Part004
    + surrogateDiagTailX0RatChunk001Sub000Block053Part005
    + surrogateDiagTailX0RatChunk001Sub000Block053Part006
    + surrogateDiagTailX0RatChunk001Sub000Block053Part007
    + surrogateDiagTailX0RatChunk001Sub000Block053Part008
    + surrogateDiagTailX0RatChunk001Sub000Block053Part009

def surrogateDiagonalTailChunk001Sub000Block053MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block053Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block053Part010
    + surrogateDiagTailX0RatChunk001Sub000Block053Part011
    + surrogateDiagTailX0RatChunk001Sub000Block053Part012
    + surrogateDiagTailX0RatChunk001Sub000Block053Part013
    + surrogateDiagTailX0RatChunk001Sub000Block053Part014
    + surrogateDiagTailX0RatChunk001Sub000Block053Part015
    + surrogateDiagTailX0RatChunk001Sub000Block053Part016
    + surrogateDiagTailX0RatChunk001Sub000Block053Part017
    + surrogateDiagTailX0RatChunk001Sub000Block053Part018
    + surrogateDiagTailX0RatChunk001Sub000Block053Part019

def surrogateDiagonalTailChunk001Sub000Block053TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block053Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block053Part020
    + surrogateDiagTailX0RatChunk001Sub000Block053Part021
    + surrogateDiagTailX0RatChunk001Sub000Block053Part022
    + surrogateDiagTailX0RatChunk001Sub000Block053Part023
    + surrogateDiagTailX0RatChunk001Sub000Block053Part024

def surrogateDiagonalTailChunk001Sub000Block053Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block053HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block053MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block053TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block053 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block053Part000
    + surrogateDiagTailX0RatChunk001Sub000Block053Part001
    + surrogateDiagTailX0RatChunk001Sub000Block053Part002
    + surrogateDiagTailX0RatChunk001Sub000Block053Part003
    + surrogateDiagTailX0RatChunk001Sub000Block053Part004
    + surrogateDiagTailX0RatChunk001Sub000Block053Part005
    + surrogateDiagTailX0RatChunk001Sub000Block053Part006
    + surrogateDiagTailX0RatChunk001Sub000Block053Part007
    + surrogateDiagTailX0RatChunk001Sub000Block053Part008
    + surrogateDiagTailX0RatChunk001Sub000Block053Part009
    + surrogateDiagTailX0RatChunk001Sub000Block053Part010
    + surrogateDiagTailX0RatChunk001Sub000Block053Part011
    + surrogateDiagTailX0RatChunk001Sub000Block053Part012
    + surrogateDiagTailX0RatChunk001Sub000Block053Part013
    + surrogateDiagTailX0RatChunk001Sub000Block053Part014
    + surrogateDiagTailX0RatChunk001Sub000Block053Part015
    + surrogateDiagTailX0RatChunk001Sub000Block053Part016
    + surrogateDiagTailX0RatChunk001Sub000Block053Part017
    + surrogateDiagTailX0RatChunk001Sub000Block053Part018
    + surrogateDiagTailX0RatChunk001Sub000Block053Part019
    + surrogateDiagTailX0RatChunk001Sub000Block053Part020
    + surrogateDiagTailX0RatChunk001Sub000Block053Part021
    + surrogateDiagTailX0RatChunk001Sub000Block053Part022
    + surrogateDiagTailX0RatChunk001Sub000Block053Part023
    + surrogateDiagTailX0RatChunk001Sub000Block053Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block053_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block053Head + surrogateDiagTailX0RatChunk001Sub000Block053Mid + surrogateDiagTailX0RatChunk001Sub000Block053Tail =
      surrogateDiagTailX0RatChunk001Sub000Block053 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block053Head surrogateDiagTailX0RatChunk001Sub000Block053Mid surrogateDiagTailX0RatChunk001Sub000Block053Tail surrogateDiagTailX0RatChunk001Sub000Block053
  ring

def SurrogateDiagonalTailChunk001Sub000Block053HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block053HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block053Head

def SurrogateDiagonalTailChunk001Sub000Block053MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block053MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block053Mid

def SurrogateDiagonalTailChunk001Sub000Block053TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block053TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block053Tail

theorem surrogateDiagonalTailChunk001Sub000Block053_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block053HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block053MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block053TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block053Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block053 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block053HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block053MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block053TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block053Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block053_eq_head_add_mid_add_tail

/-- Block 054 covers tail-support indices [11350,11375) and q from 18713 to 18754. -/

def TailChunk001Sub000Block054Part000SupportExplicit : Finset ℕ :=
  ([18713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block054Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18713
    = surrogateDiagTailX0RatChunk001Sub000Block054Part000

theorem surrogateDiagonalTailChunk001Sub000Block054Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part000] using hcert

def TailChunk001Sub000Block054Part001SupportExplicit : Finset ℕ :=
  ([18714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part001 : ℚ :=
  (304122679775 : ℚ) / 1890694188460567104

def SurrogateDiagonalTailChunk001Sub000Block054Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18714
    = surrogateDiagTailX0RatChunk001Sub000Block054Part001

theorem surrogateDiagonalTailChunk001Sub000Block054Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part001] using hcert

def TailChunk001Sub000Block054Part002SupportExplicit : Finset ℕ :=
  ([18715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part002 : ℚ :=
  (148277320225 : ℚ) / 14167169502084071424

def SurrogateDiagonalTailChunk001Sub000Block054Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18715
    = surrogateDiagTailX0RatChunk001Sub000Block054Part002

theorem surrogateDiagonalTailChunk001Sub000Block054Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part002] using hcert

def TailChunk001Sub000Block054Part003SupportExplicit : Finset ℕ :=
  ([18717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part003 : ℚ :=
  (28464006275 : ℚ) / 5881134703570845696

def SurrogateDiagonalTailChunk001Sub000Block054Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18717
    = surrogateDiagTailX0RatChunk001Sub000Block054Part003

theorem surrogateDiagonalTailChunk001Sub000Block054Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part003] using hcert

def TailChunk001Sub000Block054Part004SupportExplicit : Finset ℕ :=
  ([18719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block054Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18719
    = surrogateDiagTailX0RatChunk001Sub000Block054Part004

theorem surrogateDiagonalTailChunk001Sub000Block054Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part004] using hcert

def TailChunk001Sub000Block054Part005SupportExplicit : Finset ℕ :=
  ([18721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part005 : ℚ :=
  (9984616525 : ℚ) / 32068171417761349632

def SurrogateDiagonalTailChunk001Sub000Block054Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18721
    = surrogateDiagTailX0RatChunk001Sub000Block054Part005

theorem surrogateDiagonalTailChunk001Sub000Block054Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part005] using hcert

def TailChunk001Sub000Block054Part006SupportExplicit : Finset ℕ :=
  ([18722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part006 : ℚ :=
  (1027122931 : ℚ) / 24596176107571200

def SurrogateDiagonalTailChunk001Sub000Block054Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18722
    = surrogateDiagTailX0RatChunk001Sub000Block054Part006

theorem surrogateDiagonalTailChunk001Sub000Block054Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part006] using hcert

def TailChunk001Sub000Block054Part007SupportExplicit : Finset ℕ :=
  ([18726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part007 : ℚ :=
  (1218050219 : ℚ) / 7582199605493760

def SurrogateDiagonalTailChunk001Sub000Block054Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18726
    = surrogateDiagTailX0RatChunk001Sub000Block054Part007

theorem surrogateDiagonalTailChunk001Sub000Block054Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part007] using hcert

def TailChunk001Sub000Block054Part008SupportExplicit : Finset ℕ :=
  ([18727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part008 : ℚ :=
  (896905571 : ℚ) / 2273042486156912640

def SurrogateDiagonalTailChunk001Sub000Block054Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18727
    = surrogateDiagTailX0RatChunk001Sub000Block054Part008

theorem surrogateDiagonalTailChunk001Sub000Block054Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part008] using hcert

def TailChunk001Sub000Block054Part009SupportExplicit : Finset ℕ :=
  ([18730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part009 : ℚ :=
  (329029625225 : ℚ) / 3930612275487965184

def SurrogateDiagonalTailChunk001Sub000Block054Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18730
    = surrogateDiagTailX0RatChunk001Sub000Block054Part009

theorem surrogateDiagonalTailChunk001Sub000Block054Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part009] using hcert

def TailChunk001Sub000Block054Part010SupportExplicit : Finset ℕ :=
  ([18731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block054Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18731
    = surrogateDiagTailX0RatChunk001Sub000Block054Part010

theorem surrogateDiagonalTailChunk001Sub000Block054Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part010] using hcert

def TailChunk001Sub000Block054Part011SupportExplicit : Finset ℕ :=
  ([18733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part011 : ℚ :=
  (4743915347 : ℚ) / 740449180224000000

def SurrogateDiagonalTailChunk001Sub000Block054Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18733
    = surrogateDiagTailX0RatChunk001Sub000Block054Part011

theorem surrogateDiagonalTailChunk001Sub000Block054Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part011] using hcert

def TailChunk001Sub000Block054Part012SupportExplicit : Finset ℕ :=
  ([18734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part012 : ℚ :=
  (367893370525 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk001Sub000Block054Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18734
    = surrogateDiagTailX0RatChunk001Sub000Block054Part012

theorem surrogateDiagonalTailChunk001Sub000Block054Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part012] using hcert

def TailChunk001Sub000Block054Part013SupportExplicit : Finset ℕ :=
  ([18735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part013 : ℚ :=
  (684024655525 : ℚ) / 24845351667281952768

def SurrogateDiagonalTailChunk001Sub000Block054Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18735
    = surrogateDiagTailX0RatChunk001Sub000Block054Part013

theorem surrogateDiagonalTailChunk001Sub000Block054Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part013] using hcert

def TailChunk001Sub000Block054Part014SupportExplicit : Finset ℕ :=
  ([18737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part014 : ℚ :=
  (10889497 : ℚ) / 19422777295503360

def SurrogateDiagonalTailChunk001Sub000Block054Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18737
    = surrogateDiagTailX0RatChunk001Sub000Block054Part014

theorem surrogateDiagonalTailChunk001Sub000Block054Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part014] using hcert

def TailChunk001Sub000Block054Part015SupportExplicit : Finset ℕ :=
  ([18739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part015 : ℚ :=
  (448408898375 : ℚ) / 83089529764609434624

def SurrogateDiagonalTailChunk001Sub000Block054Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18739
    = surrogateDiagTailX0RatChunk001Sub000Block054Part015

theorem surrogateDiagonalTailChunk001Sub000Block054Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part015] using hcert

def TailChunk001Sub000Block054Part016SupportExplicit : Finset ℕ :=
  ([18741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part016 : ℚ :=
  (41675 : ℚ) / 4058603745734016

def SurrogateDiagonalTailChunk001Sub000Block054Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18741
    = surrogateDiagTailX0RatChunk001Sub000Block054Part016

theorem surrogateDiagonalTailChunk001Sub000Block054Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part016] using hcert

def TailChunk001Sub000Block054Part017SupportExplicit : Finset ℕ :=
  ([18742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block054Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18742
    = surrogateDiagTailX0RatChunk001Sub000Block054Part017

theorem surrogateDiagonalTailChunk001Sub000Block054Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part017] using hcert

def TailChunk001Sub000Block054Part018SupportExplicit : Finset ℕ :=
  ([18743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block054Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18743
    = surrogateDiagTailX0RatChunk001Sub000Block054Part018

theorem surrogateDiagonalTailChunk001Sub000Block054Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part018] using hcert

def TailChunk001Sub000Block054Part019SupportExplicit : Finset ℕ :=
  ([18745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part019 : ℚ :=
  (339478581575 : ℚ) / 34426775774245257216

def SurrogateDiagonalTailChunk001Sub000Block054Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18745
    = surrogateDiagTailX0RatChunk001Sub000Block054Part019

theorem surrogateDiagonalTailChunk001Sub000Block054Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part019] using hcert

def TailChunk001Sub000Block054Part020SupportExplicit : Finset ℕ :=
  ([18746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part020 : ℚ :=
  (9135567475 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk001Sub000Block054Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18746
    = surrogateDiagTailX0RatChunk001Sub000Block054Part020

theorem surrogateDiagonalTailChunk001Sub000Block054Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part020] using hcert

def TailChunk001Sub000Block054Part021SupportExplicit : Finset ℕ :=
  ([18749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block054Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18749
    = surrogateDiagTailX0RatChunk001Sub000Block054Part021

theorem surrogateDiagonalTailChunk001Sub000Block054Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part021] using hcert

def TailChunk001Sub000Block054Part022SupportExplicit : Finset ℕ :=
  ([18751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part022 : ℚ :=
  (308417666275 : ℚ) / 241675801498590117888

def SurrogateDiagonalTailChunk001Sub000Block054Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18751
    = surrogateDiagTailX0RatChunk001Sub000Block054Part022

theorem surrogateDiagonalTailChunk001Sub000Block054Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part022] using hcert

def TailChunk001Sub000Block054Part023SupportExplicit : Finset ℕ :=
  ([18753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part023 : ℚ :=
  (2239369337275 : ℚ) / 24370991051108548608

def SurrogateDiagonalTailChunk001Sub000Block054Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18753
    = surrogateDiagTailX0RatChunk001Sub000Block054Part023

theorem surrogateDiagonalTailChunk001Sub000Block054Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part023] using hcert

def TailChunk001Sub000Block054Part024SupportExplicit : Finset ℕ :=
  ([18754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block054Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block054Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18754
    = surrogateDiagTailX0RatChunk001Sub000Block054Part024

theorem surrogateDiagonalTailChunk001Sub000Block054Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block054Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block054Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block054Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block054Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block054Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block054HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block054Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block054Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block054Part000
    + surrogateDiagTailX0RatChunk001Sub000Block054Part001
    + surrogateDiagTailX0RatChunk001Sub000Block054Part002
    + surrogateDiagTailX0RatChunk001Sub000Block054Part003
    + surrogateDiagTailX0RatChunk001Sub000Block054Part004
    + surrogateDiagTailX0RatChunk001Sub000Block054Part005
    + surrogateDiagTailX0RatChunk001Sub000Block054Part006
    + surrogateDiagTailX0RatChunk001Sub000Block054Part007
    + surrogateDiagTailX0RatChunk001Sub000Block054Part008
    + surrogateDiagTailX0RatChunk001Sub000Block054Part009

def surrogateDiagonalTailChunk001Sub000Block054MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block054Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block054Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block054Part010
    + surrogateDiagTailX0RatChunk001Sub000Block054Part011
    + surrogateDiagTailX0RatChunk001Sub000Block054Part012
    + surrogateDiagTailX0RatChunk001Sub000Block054Part013
    + surrogateDiagTailX0RatChunk001Sub000Block054Part014
    + surrogateDiagTailX0RatChunk001Sub000Block054Part015
    + surrogateDiagTailX0RatChunk001Sub000Block054Part016
    + surrogateDiagTailX0RatChunk001Sub000Block054Part017
    + surrogateDiagTailX0RatChunk001Sub000Block054Part018
    + surrogateDiagTailX0RatChunk001Sub000Block054Part019

def surrogateDiagonalTailChunk001Sub000Block054TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block054Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block054Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block054Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block054Part020
    + surrogateDiagTailX0RatChunk001Sub000Block054Part021
    + surrogateDiagTailX0RatChunk001Sub000Block054Part022
    + surrogateDiagTailX0RatChunk001Sub000Block054Part023
    + surrogateDiagTailX0RatChunk001Sub000Block054Part024

def surrogateDiagonalTailChunk001Sub000Block054Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block054HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block054MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block054TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block054 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block054Part000
    + surrogateDiagTailX0RatChunk001Sub000Block054Part001
    + surrogateDiagTailX0RatChunk001Sub000Block054Part002
    + surrogateDiagTailX0RatChunk001Sub000Block054Part003
    + surrogateDiagTailX0RatChunk001Sub000Block054Part004
    + surrogateDiagTailX0RatChunk001Sub000Block054Part005
    + surrogateDiagTailX0RatChunk001Sub000Block054Part006
    + surrogateDiagTailX0RatChunk001Sub000Block054Part007
    + surrogateDiagTailX0RatChunk001Sub000Block054Part008
    + surrogateDiagTailX0RatChunk001Sub000Block054Part009
    + surrogateDiagTailX0RatChunk001Sub000Block054Part010
    + surrogateDiagTailX0RatChunk001Sub000Block054Part011
    + surrogateDiagTailX0RatChunk001Sub000Block054Part012
    + surrogateDiagTailX0RatChunk001Sub000Block054Part013
    + surrogateDiagTailX0RatChunk001Sub000Block054Part014
    + surrogateDiagTailX0RatChunk001Sub000Block054Part015
    + surrogateDiagTailX0RatChunk001Sub000Block054Part016
    + surrogateDiagTailX0RatChunk001Sub000Block054Part017
    + surrogateDiagTailX0RatChunk001Sub000Block054Part018
    + surrogateDiagTailX0RatChunk001Sub000Block054Part019
    + surrogateDiagTailX0RatChunk001Sub000Block054Part020
    + surrogateDiagTailX0RatChunk001Sub000Block054Part021
    + surrogateDiagTailX0RatChunk001Sub000Block054Part022
    + surrogateDiagTailX0RatChunk001Sub000Block054Part023
    + surrogateDiagTailX0RatChunk001Sub000Block054Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block054_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block054Head + surrogateDiagTailX0RatChunk001Sub000Block054Mid + surrogateDiagTailX0RatChunk001Sub000Block054Tail =
      surrogateDiagTailX0RatChunk001Sub000Block054 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block054Head surrogateDiagTailX0RatChunk001Sub000Block054Mid surrogateDiagTailX0RatChunk001Sub000Block054Tail surrogateDiagTailX0RatChunk001Sub000Block054
  ring

def SurrogateDiagonalTailChunk001Sub000Block054HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block054HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block054Head

def SurrogateDiagonalTailChunk001Sub000Block054MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block054MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block054Mid

def SurrogateDiagonalTailChunk001Sub000Block054TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block054TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block054Tail

theorem surrogateDiagonalTailChunk001Sub000Block054_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block054HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block054MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block054TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block054Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block054 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block054HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block054MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block054TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block054Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block054_eq_head_add_mid_add_tail

/-- Block 055 covers tail-support indices [11375,11400) and q from 18757 to 18799. -/

def TailChunk001Sub000Block055Part000SupportExplicit : Finset ℕ :=
  ([18757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block055Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18757
    = surrogateDiagTailX0RatChunk001Sub000Block055Part000

theorem surrogateDiagonalTailChunk001Sub000Block055Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part000] using hcert

def TailChunk001Sub000Block055Part001SupportExplicit : Finset ℕ :=
  ([18758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part001 : ℚ :=
  (2520525375 : ℚ) / 741213153026834432

def SurrogateDiagonalTailChunk001Sub000Block055Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18758
    = surrogateDiagTailX0RatChunk001Sub000Block055Part001

theorem surrogateDiagonalTailChunk001Sub000Block055Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part001] using hcert

def TailChunk001Sub000Block055Part002SupportExplicit : Finset ℕ :=
  ([18761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part002 : ℚ :=
  (99889611175 : ℚ) / 288613542759852146688

def SurrogateDiagonalTailChunk001Sub000Block055Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18761
    = surrogateDiagTailX0RatChunk001Sub000Block055Part002

theorem surrogateDiagonalTailChunk001Sub000Block055Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part002] using hcert

def TailChunk001Sub000Block055Part003SupportExplicit : Finset ℕ :=
  ([18762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part003 : ℚ :=
  (301260779575 : ℚ) / 827584215921795072

def SurrogateDiagonalTailChunk001Sub000Block055Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18762
    = surrogateDiagTailX0RatChunk001Sub000Block055Part003

theorem surrogateDiagonalTailChunk001Sub000Block055Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part003] using hcert

def TailChunk001Sub000Block055Part004SupportExplicit : Finset ℕ :=
  ([18763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part004 : ℚ :=
  (2128407675 : ℚ) / 2624151378809949184

def SurrogateDiagonalTailChunk001Sub000Block055Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18763
    = surrogateDiagTailX0RatChunk001Sub000Block055Part004

theorem surrogateDiagonalTailChunk001Sub000Block055Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part004] using hcert

def TailChunk001Sub000Block055Part005SupportExplicit : Finset ℕ :=
  ([18766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part005 : ℚ :=
  (1100274529 : ℚ) / 52704200453944320

def SurrogateDiagonalTailChunk001Sub000Block055Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18766
    = surrogateDiagTailX0RatChunk001Sub000Block055Part005

theorem surrogateDiagonalTailChunk001Sub000Block055Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part005] using hcert

def TailChunk001Sub000Block055Part006SupportExplicit : Finset ℕ :=
  ([18770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part006 : ℚ :=
  (47204937425 : ℚ) / 566330725982257152

def SurrogateDiagonalTailChunk001Sub000Block055Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18770
    = surrogateDiagTailX0RatChunk001Sub000Block055Part006

theorem surrogateDiagonalTailChunk001Sub000Block055Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part006] using hcert

def TailChunk001Sub000Block055Part007SupportExplicit : Finset ℕ :=
  ([18771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part007 : ℚ :=
  (611680257775 : ℚ) / 15320530734961262592

def SurrogateDiagonalTailChunk001Sub000Block055Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18771
    = surrogateDiagTailX0RatChunk001Sub000Block055Part007

theorem surrogateDiagonalTailChunk001Sub000Block055Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part007] using hcert

def TailChunk001Sub000Block055Part008SupportExplicit : Finset ℕ :=
  ([18773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block055Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18773
    = surrogateDiagTailX0RatChunk001Sub000Block055Part008

theorem surrogateDiagonalTailChunk001Sub000Block055Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part008] using hcert

def TailChunk001Sub000Block055Part009SupportExplicit : Finset ℕ :=
  ([18777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part009 : ℚ :=
  (31538990697 : ℚ) / 555237667333734400

def SurrogateDiagonalTailChunk001Sub000Block055Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18777
    = surrogateDiagTailX0RatChunk001Sub000Block055Part009

theorem surrogateDiagonalTailChunk001Sub000Block055Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part009] using hcert

def TailChunk001Sub000Block055Part010SupportExplicit : Finset ℕ :=
  ([18778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part010 : ℚ :=
  (52300603 : ℚ) / 10811506893004800

def SurrogateDiagonalTailChunk001Sub000Block055Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18778
    = surrogateDiagTailX0RatChunk001Sub000Block055Part010

theorem surrogateDiagonalTailChunk001Sub000Block055Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part010] using hcert

def TailChunk001Sub000Block055Part011SupportExplicit : Finset ℕ :=
  ([18779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part011 : ℚ :=
  (104149531 : ℚ) / 324035219941171200

def SurrogateDiagonalTailChunk001Sub000Block055Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18779
    = surrogateDiagTailX0RatChunk001Sub000Block055Part011

theorem surrogateDiagonalTailChunk001Sub000Block055Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part011] using hcert

def TailChunk001Sub000Block055Part012SupportExplicit : Finset ℕ :=
  ([18781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part012 : ℚ :=
  (450417746675 : ℚ) / 83837237359242037824

def SurrogateDiagonalTailChunk001Sub000Block055Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18781
    = surrogateDiagTailX0RatChunk001Sub000Block055Part012

theorem surrogateDiagonalTailChunk001Sub000Block055Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part012] using hcert

def TailChunk001Sub000Block055Part013SupportExplicit : Finset ℕ :=
  ([18782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block055Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18782
    = surrogateDiagTailX0RatChunk001Sub000Block055Part013

theorem surrogateDiagonalTailChunk001Sub000Block055Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part013] using hcert

def TailChunk001Sub000Block055Part014SupportExplicit : Finset ℕ :=
  ([18786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part014 : ℚ :=
  (48137286601 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk001Sub000Block055Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18786
    = surrogateDiagTailX0RatChunk001Sub000Block055Part014

theorem surrogateDiagonalTailChunk001Sub000Block055Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part014] using hcert

def TailChunk001Sub000Block055Part015SupportExplicit : Finset ℕ :=
  ([18787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block055Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18787
    = surrogateDiagTailX0RatChunk001Sub000Block055Part015

theorem surrogateDiagonalTailChunk001Sub000Block055Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part015] using hcert

def TailChunk001Sub000Block055Part016SupportExplicit : Finset ℕ :=
  ([18789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part016 : ℚ :=
  (1225707640475 : ℚ) / 30758779515212602944

def SurrogateDiagonalTailChunk001Sub000Block055Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18789
    = surrogateDiagTailX0RatChunk001Sub000Block055Part016

theorem surrogateDiagonalTailChunk001Sub000Block055Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part016] using hcert

def TailChunk001Sub000Block055Part017SupportExplicit : Finset ℕ :=
  ([18790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part017 : ℚ :=
  (147340963075 : ℚ) / 2654165020075923456

def SurrogateDiagonalTailChunk001Sub000Block055Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18790
    = surrogateDiagTailX0RatChunk001Sub000Block055Part017

theorem surrogateDiagonalTailChunk001Sub000Block055Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part017] using hcert

def TailChunk001Sub000Block055Part018SupportExplicit : Finset ℕ :=
  ([18791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part018 : ℚ :=
  (647315258875 : ℚ) / 191339557023062181888

def SurrogateDiagonalTailChunk001Sub000Block055Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18791
    = surrogateDiagTailX0RatChunk001Sub000Block055Part018

theorem surrogateDiagonalTailChunk001Sub000Block055Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part018] using hcert

def TailChunk001Sub000Block055Part019SupportExplicit : Finset ℕ :=
  ([18793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block055Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18793
    = surrogateDiagTailX0RatChunk001Sub000Block055Part019

theorem surrogateDiagonalTailChunk001Sub000Block055Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part019] using hcert

def TailChunk001Sub000Block055Part020SupportExplicit : Finset ℕ :=
  ([18794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block055Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18794
    = surrogateDiagTailX0RatChunk001Sub000Block055Part020

theorem surrogateDiagonalTailChunk001Sub000Block055Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part020] using hcert

def TailChunk001Sub000Block055Part021SupportExplicit : Finset ℕ :=
  ([18795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part021 : ℚ :=
  (501296957425 : ℚ) / 3331285283834560512

def SurrogateDiagonalTailChunk001Sub000Block055Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18795
    = surrogateDiagTailX0RatChunk001Sub000Block055Part021

theorem surrogateDiagonalTailChunk001Sub000Block055Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part021] using hcert

def TailChunk001Sub000Block055Part022SupportExplicit : Finset ℕ :=
  ([18797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block055Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18797
    = surrogateDiagTailX0RatChunk001Sub000Block055Part022

theorem surrogateDiagonalTailChunk001Sub000Block055Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part022] using hcert

def TailChunk001Sub000Block055Part023SupportExplicit : Finset ℕ :=
  ([18798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part023 : ℚ :=
  (11880264679 : ℚ) / 27524332309708800

def SurrogateDiagonalTailChunk001Sub000Block055Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18798
    = surrogateDiagTailX0RatChunk001Sub000Block055Part023

theorem surrogateDiagonalTailChunk001Sub000Block055Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part023] using hcert

def TailChunk001Sub000Block055Part024SupportExplicit : Finset ℕ :=
  ([18799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block055Part024 : ℚ :=
  (3142260691 : ℚ) / 1216018761649305600

def SurrogateDiagonalTailChunk001Sub000Block055Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18799
    = surrogateDiagTailX0RatChunk001Sub000Block055Part024

theorem surrogateDiagonalTailChunk001Sub000Block055Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block055Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block055Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block055Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block055Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block055Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block055HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block055Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block055Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block055Part000
    + surrogateDiagTailX0RatChunk001Sub000Block055Part001
    + surrogateDiagTailX0RatChunk001Sub000Block055Part002
    + surrogateDiagTailX0RatChunk001Sub000Block055Part003
    + surrogateDiagTailX0RatChunk001Sub000Block055Part004
    + surrogateDiagTailX0RatChunk001Sub000Block055Part005
    + surrogateDiagTailX0RatChunk001Sub000Block055Part006
    + surrogateDiagTailX0RatChunk001Sub000Block055Part007
    + surrogateDiagTailX0RatChunk001Sub000Block055Part008
    + surrogateDiagTailX0RatChunk001Sub000Block055Part009

def surrogateDiagonalTailChunk001Sub000Block055MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block055Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block055Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block055Part010
    + surrogateDiagTailX0RatChunk001Sub000Block055Part011
    + surrogateDiagTailX0RatChunk001Sub000Block055Part012
    + surrogateDiagTailX0RatChunk001Sub000Block055Part013
    + surrogateDiagTailX0RatChunk001Sub000Block055Part014
    + surrogateDiagTailX0RatChunk001Sub000Block055Part015
    + surrogateDiagTailX0RatChunk001Sub000Block055Part016
    + surrogateDiagTailX0RatChunk001Sub000Block055Part017
    + surrogateDiagTailX0RatChunk001Sub000Block055Part018
    + surrogateDiagTailX0RatChunk001Sub000Block055Part019

def surrogateDiagonalTailChunk001Sub000Block055TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block055Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block055Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block055Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block055Part020
    + surrogateDiagTailX0RatChunk001Sub000Block055Part021
    + surrogateDiagTailX0RatChunk001Sub000Block055Part022
    + surrogateDiagTailX0RatChunk001Sub000Block055Part023
    + surrogateDiagTailX0RatChunk001Sub000Block055Part024

def surrogateDiagonalTailChunk001Sub000Block055Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block055HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block055MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block055TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block055 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block055Part000
    + surrogateDiagTailX0RatChunk001Sub000Block055Part001
    + surrogateDiagTailX0RatChunk001Sub000Block055Part002
    + surrogateDiagTailX0RatChunk001Sub000Block055Part003
    + surrogateDiagTailX0RatChunk001Sub000Block055Part004
    + surrogateDiagTailX0RatChunk001Sub000Block055Part005
    + surrogateDiagTailX0RatChunk001Sub000Block055Part006
    + surrogateDiagTailX0RatChunk001Sub000Block055Part007
    + surrogateDiagTailX0RatChunk001Sub000Block055Part008
    + surrogateDiagTailX0RatChunk001Sub000Block055Part009
    + surrogateDiagTailX0RatChunk001Sub000Block055Part010
    + surrogateDiagTailX0RatChunk001Sub000Block055Part011
    + surrogateDiagTailX0RatChunk001Sub000Block055Part012
    + surrogateDiagTailX0RatChunk001Sub000Block055Part013
    + surrogateDiagTailX0RatChunk001Sub000Block055Part014
    + surrogateDiagTailX0RatChunk001Sub000Block055Part015
    + surrogateDiagTailX0RatChunk001Sub000Block055Part016
    + surrogateDiagTailX0RatChunk001Sub000Block055Part017
    + surrogateDiagTailX0RatChunk001Sub000Block055Part018
    + surrogateDiagTailX0RatChunk001Sub000Block055Part019
    + surrogateDiagTailX0RatChunk001Sub000Block055Part020
    + surrogateDiagTailX0RatChunk001Sub000Block055Part021
    + surrogateDiagTailX0RatChunk001Sub000Block055Part022
    + surrogateDiagTailX0RatChunk001Sub000Block055Part023
    + surrogateDiagTailX0RatChunk001Sub000Block055Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block055_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block055Head + surrogateDiagTailX0RatChunk001Sub000Block055Mid + surrogateDiagTailX0RatChunk001Sub000Block055Tail =
      surrogateDiagTailX0RatChunk001Sub000Block055 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block055Head surrogateDiagTailX0RatChunk001Sub000Block055Mid surrogateDiagTailX0RatChunk001Sub000Block055Tail surrogateDiagTailX0RatChunk001Sub000Block055
  ring

def SurrogateDiagonalTailChunk001Sub000Block055HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block055HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block055Head

def SurrogateDiagonalTailChunk001Sub000Block055MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block055MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block055Mid

def SurrogateDiagonalTailChunk001Sub000Block055TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block055TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block055Tail

theorem surrogateDiagonalTailChunk001Sub000Block055_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block055HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block055MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block055TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block055Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block055 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block055HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block055MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block055TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block055Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block055_eq_head_add_mid_add_tail

/-- Block 056 covers tail-support indices [11400,11425) and q from 18802 to 18841. -/

def TailChunk001Sub000Block056Part000SupportExplicit : Finset ℕ :=
  ([18802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part000 : ℚ :=
  (280620738875 : ℚ) / 3930612275487965184

def SurrogateDiagonalTailChunk001Sub000Block056Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18802
    = surrogateDiagTailX0RatChunk001Sub000Block056Part000

theorem surrogateDiagonalTailChunk001Sub000Block056Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part000] using hcert

def TailChunk001Sub000Block056Part001SupportExplicit : Finset ℕ :=
  ([18803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block056Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18803
    = surrogateDiagTailX0RatChunk001Sub000Block056Part001

theorem surrogateDiagonalTailChunk001Sub000Block056Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part001] using hcert

def TailChunk001Sub000Block056Part002SupportExplicit : Finset ℕ :=
  ([18805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part002 : ℚ :=
  (1504763027 : ℚ) / 108888079309209600

def SurrogateDiagonalTailChunk001Sub000Block056Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18805
    = surrogateDiagTailX0RatChunk001Sub000Block056Part002

theorem surrogateDiagonalTailChunk001Sub000Block056Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part002] using hcert

def TailChunk001Sub000Block056Part003SupportExplicit : Finset ℕ :=
  ([18806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block056Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18806
    = surrogateDiagTailX0RatChunk001Sub000Block056Part003

theorem surrogateDiagonalTailChunk001Sub000Block056Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part003] using hcert

def TailChunk001Sub000Block056Part004SupportExplicit : Finset ℕ :=
  ([18807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part004 : ℚ :=
  (153507126925 : ℚ) / 3859604553194767488

def SurrogateDiagonalTailChunk001Sub000Block056Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18807
    = surrogateDiagTailX0RatChunk001Sub000Block056Part004

theorem surrogateDiagonalTailChunk001Sub000Block056Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part004] using hcert

def TailChunk001Sub000Block056Part005SupportExplicit : Finset ℕ :=
  ([18809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part005 : ℚ :=
  (452787134125 : ℚ) / 168677009892267043968

def SurrogateDiagonalTailChunk001Sub000Block056Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18809
    = surrogateDiagTailX0RatChunk001Sub000Block056Part005

theorem surrogateDiagonalTailChunk001Sub000Block056Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part005] using hcert

def TailChunk001Sub000Block056Part006SupportExplicit : Finset ℕ :=
  ([18811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part006 : ℚ :=
  (98910808675 : ℚ) / 56671541200797553152

def SurrogateDiagonalTailChunk001Sub000Block056Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18811
    = surrogateDiagTailX0RatChunk001Sub000Block056Part006

theorem surrogateDiagonalTailChunk001Sub000Block056Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part006] using hcert

def TailChunk001Sub000Block056Part007SupportExplicit : Finset ℕ :=
  ([18813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part007 : ℚ :=
  (9830725123 : ℚ) / 247330113157005120

def SurrogateDiagonalTailChunk001Sub000Block056Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18813
    = surrogateDiagTailX0RatChunk001Sub000Block056Part007

theorem surrogateDiagonalTailChunk001Sub000Block056Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part007] using hcert

def TailChunk001Sub000Block056Part008SupportExplicit : Finset ℕ :=
  ([18814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part008 : ℚ :=
  (65718481025 : ℚ) / 8115742122194386944

def SurrogateDiagonalTailChunk001Sub000Block056Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18814
    = surrogateDiagTailX0RatChunk001Sub000Block056Part008

theorem surrogateDiagonalTailChunk001Sub000Block056Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part008] using hcert

def TailChunk001Sub000Block056Part009SupportExplicit : Finset ℕ :=
  ([18815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part009 : ℚ :=
  (10320476599 : ℚ) / 642146781403545600

def SurrogateDiagonalTailChunk001Sub000Block056Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18815
    = surrogateDiagTailX0RatChunk001Sub000Block056Part009

theorem surrogateDiagonalTailChunk001Sub000Block056Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part009] using hcert

def TailChunk001Sub000Block056Part010SupportExplicit : Finset ℕ :=
  ([18817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part010 : ℚ :=
  (481803247 : ℚ) / 682876839019192200

def SurrogateDiagonalTailChunk001Sub000Block056Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18817
    = surrogateDiagTailX0RatChunk001Sub000Block056Part010

theorem surrogateDiagonalTailChunk001Sub000Block056Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part010] using hcert

def TailChunk001Sub000Block056Part011SupportExplicit : Finset ℕ :=
  ([18821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part011 : ℚ :=
  (15338258987 : ℚ) / 3478571657904537600

def SurrogateDiagonalTailChunk001Sub000Block056Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18821
    = surrogateDiagTailX0RatChunk001Sub000Block056Part011

theorem surrogateDiagonalTailChunk001Sub000Block056Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part011] using hcert

def TailChunk001Sub000Block056Part012SupportExplicit : Finset ℕ :=
  ([18822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part012 : ℚ :=
  (21974325325 : ℚ) / 138195221480472576

def SurrogateDiagonalTailChunk001Sub000Block056Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18822
    = surrogateDiagTailX0RatChunk001Sub000Block056Part012

theorem surrogateDiagonalTailChunk001Sub000Block056Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part012] using hcert

def TailChunk001Sub000Block056Part013SupportExplicit : Finset ℕ :=
  ([18823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part013 : ℚ :=
  (452431094075 : ℚ) / 84589980000781860864

def SurrogateDiagonalTailChunk001Sub000Block056Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18823
    = surrogateDiagTailX0RatChunk001Sub000Block056Part013

theorem surrogateDiagonalTailChunk001Sub000Block056Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part013] using hcert

def TailChunk001Sub000Block056Part014SupportExplicit : Finset ℕ :=
  ([18826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block056Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18826
    = surrogateDiagTailX0RatChunk001Sub000Block056Part014

theorem surrogateDiagonalTailChunk001Sub000Block056Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part014] using hcert

def TailChunk001Sub000Block056Part015SupportExplicit : Finset ℕ :=
  ([18827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part015 : ℚ :=
  (241387669 : ℚ) / 648070439882342400

def SurrogateDiagonalTailChunk001Sub000Block056Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18827
    = surrogateDiagTailX0RatChunk001Sub000Block056Part015

theorem surrogateDiagonalTailChunk001Sub000Block056Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part015] using hcert

def TailChunk001Sub000Block056Part016SupportExplicit : Finset ℕ :=
  ([18829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part016 : ℚ :=
  (6233175761 : ℚ) / 5042984732555457600

def SurrogateDiagonalTailChunk001Sub000Block056Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18829
    = surrogateDiagTailX0RatChunk001Sub000Block056Part016

theorem surrogateDiagonalTailChunk001Sub000Block056Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part016] using hcert

def TailChunk001Sub000Block056Part017SupportExplicit : Finset ℕ :=
  ([18830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part017 : ℚ :=
  (52074876775 : ℚ) / 267479818102407168

def SurrogateDiagonalTailChunk001Sub000Block056Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18830
    = surrogateDiagTailX0RatChunk001Sub000Block056Part017

theorem surrogateDiagonalTailChunk001Sub000Block056Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part017] using hcert

def TailChunk001Sub000Block056Part018SupportExplicit : Finset ℕ :=
  ([18831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part018 : ℚ :=
  (307798253825 : ℚ) / 7758693471443486976

def SurrogateDiagonalTailChunk001Sub000Block056Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18831
    = surrogateDiagTailX0RatChunk001Sub000Block056Part018

theorem surrogateDiagonalTailChunk001Sub000Block056Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part018] using hcert

def TailChunk001Sub000Block056Part019SupportExplicit : Finset ℕ :=
  ([18833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part019 : ℚ :=
  (43059979375 : ℚ) / 69924878393299771392

def SurrogateDiagonalTailChunk001Sub000Block056Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18833
    = surrogateDiagTailX0RatChunk001Sub000Block056Part019

theorem surrogateDiagonalTailChunk001Sub000Block056Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part019] using hcert

def TailChunk001Sub000Block056Part020SupportExplicit : Finset ℕ :=
  ([18834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part020 : ℚ :=
  (91562092225 : ℚ) / 477942827850399744

def SurrogateDiagonalTailChunk001Sub000Block056Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18834
    = surrogateDiagTailX0RatChunk001Sub000Block056Part020

theorem surrogateDiagonalTailChunk001Sub000Block056Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part020] using hcert

def TailChunk001Sub000Block056Part021SupportExplicit : Finset ℕ :=
  ([18835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part021 : ℚ :=
  (1773739926025 : ℚ) / 128762110636215748608

def SurrogateDiagonalTailChunk001Sub000Block056Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18835
    = surrogateDiagTailX0RatChunk001Sub000Block056Part021

theorem surrogateDiagonalTailChunk001Sub000Block056Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part021] using hcert

def TailChunk001Sub000Block056Part022SupportExplicit : Finset ℕ :=
  ([18838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block056Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18838
    = surrogateDiagTailX0RatChunk001Sub000Block056Part022

theorem surrogateDiagonalTailChunk001Sub000Block056Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part022] using hcert

def TailChunk001Sub000Block056Part023SupportExplicit : Finset ℕ :=
  ([18839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block056Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18839
    = surrogateDiagTailX0RatChunk001Sub000Block056Part023

theorem surrogateDiagonalTailChunk001Sub000Block056Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part023] using hcert

def TailChunk001Sub000Block056Part024SupportExplicit : Finset ℕ :=
  ([18841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block056Part024 : ℚ :=
  (95461953775 : ℚ) / 294928013082556380288

def SurrogateDiagonalTailChunk001Sub000Block056Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18841
    = surrogateDiagTailX0RatChunk001Sub000Block056Part024

theorem surrogateDiagonalTailChunk001Sub000Block056Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block056Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block056Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block056Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block056Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block056Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block056HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block056Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block056Part000
    + surrogateDiagTailX0RatChunk001Sub000Block056Part001
    + surrogateDiagTailX0RatChunk001Sub000Block056Part002
    + surrogateDiagTailX0RatChunk001Sub000Block056Part003
    + surrogateDiagTailX0RatChunk001Sub000Block056Part004
    + surrogateDiagTailX0RatChunk001Sub000Block056Part005
    + surrogateDiagTailX0RatChunk001Sub000Block056Part006
    + surrogateDiagTailX0RatChunk001Sub000Block056Part007
    + surrogateDiagTailX0RatChunk001Sub000Block056Part008
    + surrogateDiagTailX0RatChunk001Sub000Block056Part009

def surrogateDiagonalTailChunk001Sub000Block056MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block056Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block056Part010
    + surrogateDiagTailX0RatChunk001Sub000Block056Part011
    + surrogateDiagTailX0RatChunk001Sub000Block056Part012
    + surrogateDiagTailX0RatChunk001Sub000Block056Part013
    + surrogateDiagTailX0RatChunk001Sub000Block056Part014
    + surrogateDiagTailX0RatChunk001Sub000Block056Part015
    + surrogateDiagTailX0RatChunk001Sub000Block056Part016
    + surrogateDiagTailX0RatChunk001Sub000Block056Part017
    + surrogateDiagTailX0RatChunk001Sub000Block056Part018
    + surrogateDiagTailX0RatChunk001Sub000Block056Part019

def surrogateDiagonalTailChunk001Sub000Block056TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block056Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block056Part020
    + surrogateDiagTailX0RatChunk001Sub000Block056Part021
    + surrogateDiagTailX0RatChunk001Sub000Block056Part022
    + surrogateDiagTailX0RatChunk001Sub000Block056Part023
    + surrogateDiagTailX0RatChunk001Sub000Block056Part024

def surrogateDiagonalTailChunk001Sub000Block056Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block056HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block056MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block056TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block056 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block056Part000
    + surrogateDiagTailX0RatChunk001Sub000Block056Part001
    + surrogateDiagTailX0RatChunk001Sub000Block056Part002
    + surrogateDiagTailX0RatChunk001Sub000Block056Part003
    + surrogateDiagTailX0RatChunk001Sub000Block056Part004
    + surrogateDiagTailX0RatChunk001Sub000Block056Part005
    + surrogateDiagTailX0RatChunk001Sub000Block056Part006
    + surrogateDiagTailX0RatChunk001Sub000Block056Part007
    + surrogateDiagTailX0RatChunk001Sub000Block056Part008
    + surrogateDiagTailX0RatChunk001Sub000Block056Part009
    + surrogateDiagTailX0RatChunk001Sub000Block056Part010
    + surrogateDiagTailX0RatChunk001Sub000Block056Part011
    + surrogateDiagTailX0RatChunk001Sub000Block056Part012
    + surrogateDiagTailX0RatChunk001Sub000Block056Part013
    + surrogateDiagTailX0RatChunk001Sub000Block056Part014
    + surrogateDiagTailX0RatChunk001Sub000Block056Part015
    + surrogateDiagTailX0RatChunk001Sub000Block056Part016
    + surrogateDiagTailX0RatChunk001Sub000Block056Part017
    + surrogateDiagTailX0RatChunk001Sub000Block056Part018
    + surrogateDiagTailX0RatChunk001Sub000Block056Part019
    + surrogateDiagTailX0RatChunk001Sub000Block056Part020
    + surrogateDiagTailX0RatChunk001Sub000Block056Part021
    + surrogateDiagTailX0RatChunk001Sub000Block056Part022
    + surrogateDiagTailX0RatChunk001Sub000Block056Part023
    + surrogateDiagTailX0RatChunk001Sub000Block056Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block056_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block056Head + surrogateDiagTailX0RatChunk001Sub000Block056Mid + surrogateDiagTailX0RatChunk001Sub000Block056Tail =
      surrogateDiagTailX0RatChunk001Sub000Block056 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block056Head surrogateDiagTailX0RatChunk001Sub000Block056Mid surrogateDiagTailX0RatChunk001Sub000Block056Tail surrogateDiagTailX0RatChunk001Sub000Block056
  ring

def SurrogateDiagonalTailChunk001Sub000Block056HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block056HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block056Head

def SurrogateDiagonalTailChunk001Sub000Block056MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block056MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block056Mid

def SurrogateDiagonalTailChunk001Sub000Block056TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block056TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block056Tail

theorem surrogateDiagonalTailChunk001Sub000Block056_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block056HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block056MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block056TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block056Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block056 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block056HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block056MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block056TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block056Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block056_eq_head_add_mid_add_tail

/-- Block 057 covers tail-support indices [11425,11450) and q from 18842 to 18883. -/

def TailChunk001Sub000Block057Part000SupportExplicit : Finset ℕ :=
  ([18842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block057Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18842
    = surrogateDiagTailX0RatChunk001Sub000Block057Part000

theorem surrogateDiagonalTailChunk001Sub000Block057Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part000] using hcert

def TailChunk001Sub000Block057Part001SupportExplicit : Finset ℕ :=
  ([18843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part001 : ℚ :=
  (19056539411 : ℚ) / 337859590406400000

def SurrogateDiagonalTailChunk001Sub000Block057Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18843
    = surrogateDiagTailX0RatChunk001Sub000Block057Part001

theorem surrogateDiagonalTailChunk001Sub000Block057Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part001] using hcert

def TailChunk001Sub000Block057Part002SupportExplicit : Finset ℕ :=
  ([18845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part002 : ℚ :=
  (888614716375 : ℚ) / 129035854064795516928

def SurrogateDiagonalTailChunk001Sub000Block057Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18845
    = surrogateDiagTailX0RatChunk001Sub000Block057Part002

theorem surrogateDiagonalTailChunk001Sub000Block057Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part002] using hcert

def TailChunk001Sub000Block057Part003SupportExplicit : Finset ℕ :=
  ([18847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part003 : ℚ :=
  (5760610771 : ℚ) / 11464579817472000000

def SurrogateDiagonalTailChunk001Sub000Block057Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18847
    = surrogateDiagTailX0RatChunk001Sub000Block057Part003

theorem surrogateDiagonalTailChunk001Sub000Block057Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part003] using hcert

def TailChunk001Sub000Block057Part004SupportExplicit : Finset ℕ :=
  ([18849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part004 : ℚ :=
  (180721243 : ℚ) / 4157370802298880

def SurrogateDiagonalTailChunk001Sub000Block057Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18849
    = surrogateDiagTailX0RatChunk001Sub000Block057Part004

theorem surrogateDiagonalTailChunk001Sub000Block057Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part004] using hcert

def TailChunk001Sub000Block057Part005SupportExplicit : Finset ℕ :=
  ([18851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part005 : ℚ :=
  (453775825175 : ℚ) / 85094616812141896704

def SurrogateDiagonalTailChunk001Sub000Block057Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18851
    = surrogateDiagTailX0RatChunk001Sub000Block057Part005

theorem surrogateDiagonalTailChunk001Sub000Block057Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part005] using hcert

def TailChunk001Sub000Block057Part006SupportExplicit : Finset ℕ :=
  ([18853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part006 : ℚ :=
  (388336681525 : ℚ) / 246982300250174128128

def SurrogateDiagonalTailChunk001Sub000Block057Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18853
    = surrogateDiagTailX0RatChunk001Sub000Block057Part006

theorem surrogateDiagonalTailChunk001Sub000Block057Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part006] using hcert

def TailChunk001Sub000Block057Part007SupportExplicit : Finset ℕ :=
  ([18854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part007 : ℚ :=
  (1110512257 : ℚ) / 53700942610513920

def SurrogateDiagonalTailChunk001Sub000Block057Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18854
    = surrogateDiagTailX0RatChunk001Sub000Block057Part007

theorem surrogateDiagonalTailChunk001Sub000Block057Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part007] using hcert

def TailChunk001Sub000Block057Part008SupportExplicit : Finset ℕ :=
  ([18857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part008 : ℚ :=
  (87164106325 : ℚ) / 297738960968982233088

def SurrogateDiagonalTailChunk001Sub000Block057Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18857
    = surrogateDiagTailX0RatChunk001Sub000Block057Part008

theorem surrogateDiagonalTailChunk001Sub000Block057Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part008] using hcert

def TailChunk001Sub000Block057Part009SupportExplicit : Finset ℕ :=
  ([18858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part009 : ℚ :=
  (693741170275 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk001Sub000Block057Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18858
    = surrogateDiagTailX0RatChunk001Sub000Block057Part009

theorem surrogateDiagonalTailChunk001Sub000Block057Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part009] using hcert

def TailChunk001Sub000Block057Part010SupportExplicit : Finset ℕ :=
  ([18859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block057Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18859
    = surrogateDiagTailX0RatChunk001Sub000Block057Part010

theorem surrogateDiagonalTailChunk001Sub000Block057Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part010] using hcert

def TailChunk001Sub000Block057Part011SupportExplicit : Finset ℕ :=
  ([18861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part011 : ℚ :=
  (176445520025 : ℚ) / 4461863835269948352

def SurrogateDiagonalTailChunk001Sub000Block057Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18861
    = surrogateDiagTailX0RatChunk001Sub000Block057Part011

theorem surrogateDiagonalTailChunk001Sub000Block057Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part011] using hcert

def TailChunk001Sub000Block057Part012SupportExplicit : Finset ℕ :=
  ([18862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block057Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18862
    = surrogateDiagTailX0RatChunk001Sub000Block057Part012

theorem surrogateDiagonalTailChunk001Sub000Block057Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part012] using hcert

def TailChunk001Sub000Block057Part013SupportExplicit : Finset ℕ :=
  ([18863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part013 : ℚ :=
  (3527083099 : ℚ) / 1528032505392000000

def SurrogateDiagonalTailChunk001Sub000Block057Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18863
    = surrogateDiagTailX0RatChunk001Sub000Block057Part013

theorem surrogateDiagonalTailChunk001Sub000Block057Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part013] using hcert

def TailChunk001Sub000Block057Part014SupportExplicit : Finset ℕ :=
  ([18866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block057Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18866
    = surrogateDiagTailX0RatChunk001Sub000Block057Part014

theorem surrogateDiagonalTailChunk001Sub000Block057Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part014] using hcert

def TailChunk001Sub000Block057Part015SupportExplicit : Finset ℕ :=
  ([18867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part015 : ℚ :=
  (96553340353 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk001Sub000Block057Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18867
    = surrogateDiagTailX0RatChunk001Sub000Block057Part015

theorem surrogateDiagonalTailChunk001Sub000Block057Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part015] using hcert

def TailChunk001Sub000Block057Part016SupportExplicit : Finset ℕ :=
  ([18869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block057Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18869
    = surrogateDiagTailX0RatChunk001Sub000Block057Part016

theorem surrogateDiagonalTailChunk001Sub000Block057Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part016] using hcert

def TailChunk001Sub000Block057Part017SupportExplicit : Finset ℕ :=
  ([18870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part017 : ℚ :=
  (9383602325 : ℚ) / 5219428941692928

def SurrogateDiagonalTailChunk001Sub000Block057Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18870
    = surrogateDiagTailX0RatChunk001Sub000Block057Part017

theorem surrogateDiagonalTailChunk001Sub000Block057Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part017] using hcert

def TailChunk001Sub000Block057Part018SupportExplicit : Finset ℕ :=
  ([18871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part018 : ℚ :=
  (85246852525 : ℚ) / 298766088815887515648

def SurrogateDiagonalTailChunk001Sub000Block057Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18871
    = surrogateDiagTailX0RatChunk001Sub000Block057Part018

theorem surrogateDiagonalTailChunk001Sub000Block057Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part018] using hcert

def TailChunk001Sub000Block057Part019SupportExplicit : Finset ℕ :=
  ([18874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part019 : ℚ :=
  (1391515140625 : ℚ) / 4955855059883173152

def SurrogateDiagonalTailChunk001Sub000Block057Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18874
    = surrogateDiagTailX0RatChunk001Sub000Block057Part019

theorem surrogateDiagonalTailChunk001Sub000Block057Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part019] using hcert

def TailChunk001Sub000Block057Part020SupportExplicit : Finset ℕ :=
  ([18877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part020 : ℚ :=
  (4354647425 : ℚ) / 7954592963878921248

def SurrogateDiagonalTailChunk001Sub000Block057Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18877
    = surrogateDiagTailX0RatChunk001Sub000Block057Part020

theorem surrogateDiagonalTailChunk001Sub000Block057Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part020] using hcert

def TailChunk001Sub000Block057Part021SupportExplicit : Finset ℕ :=
  ([18878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part021 : ℚ :=
  (1392105015625 : ℚ) / 4960058053443249042

def SurrogateDiagonalTailChunk001Sub000Block057Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18878
    = surrogateDiagTailX0RatChunk001Sub000Block057Part021

theorem surrogateDiagonalTailChunk001Sub000Block057Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part021] using hcert

def TailChunk001Sub000Block057Part022SupportExplicit : Finset ℕ :=
  ([18879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part022 : ℚ :=
  (3305279731 : ℚ) / 38244167752089600

def SurrogateDiagonalTailChunk001Sub000Block057Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18879
    = surrogateDiagTailX0RatChunk001Sub000Block057Part022

theorem surrogateDiagonalTailChunk001Sub000Block057Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part022] using hcert

def TailChunk001Sub000Block057Part023SupportExplicit : Finset ℕ :=
  ([18881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part023 : ℚ :=
  (7292645725 : ℚ) / 22843873447931442816

def SurrogateDiagonalTailChunk001Sub000Block057Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18881
    = surrogateDiagTailX0RatChunk001Sub000Block057Part023

theorem surrogateDiagonalTailChunk001Sub000Block057Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part023] using hcert

def TailChunk001Sub000Block057Part024SupportExplicit : Finset ℕ :=
  ([18883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block057Part024 : ℚ :=
  (414020143 : ℚ) / 423733669830248448

def SurrogateDiagonalTailChunk001Sub000Block057Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18883
    = surrogateDiagTailX0RatChunk001Sub000Block057Part024

theorem surrogateDiagonalTailChunk001Sub000Block057Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block057Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block057Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block057Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block057Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block057Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block057HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block057Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block057Part000
    + surrogateDiagTailX0RatChunk001Sub000Block057Part001
    + surrogateDiagTailX0RatChunk001Sub000Block057Part002
    + surrogateDiagTailX0RatChunk001Sub000Block057Part003
    + surrogateDiagTailX0RatChunk001Sub000Block057Part004
    + surrogateDiagTailX0RatChunk001Sub000Block057Part005
    + surrogateDiagTailX0RatChunk001Sub000Block057Part006
    + surrogateDiagTailX0RatChunk001Sub000Block057Part007
    + surrogateDiagTailX0RatChunk001Sub000Block057Part008
    + surrogateDiagTailX0RatChunk001Sub000Block057Part009

def surrogateDiagonalTailChunk001Sub000Block057MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block057Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block057Part010
    + surrogateDiagTailX0RatChunk001Sub000Block057Part011
    + surrogateDiagTailX0RatChunk001Sub000Block057Part012
    + surrogateDiagTailX0RatChunk001Sub000Block057Part013
    + surrogateDiagTailX0RatChunk001Sub000Block057Part014
    + surrogateDiagTailX0RatChunk001Sub000Block057Part015
    + surrogateDiagTailX0RatChunk001Sub000Block057Part016
    + surrogateDiagTailX0RatChunk001Sub000Block057Part017
    + surrogateDiagTailX0RatChunk001Sub000Block057Part018
    + surrogateDiagTailX0RatChunk001Sub000Block057Part019

def surrogateDiagonalTailChunk001Sub000Block057TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block057Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block057Part020
    + surrogateDiagTailX0RatChunk001Sub000Block057Part021
    + surrogateDiagTailX0RatChunk001Sub000Block057Part022
    + surrogateDiagTailX0RatChunk001Sub000Block057Part023
    + surrogateDiagTailX0RatChunk001Sub000Block057Part024

def surrogateDiagonalTailChunk001Sub000Block057Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block057HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block057MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block057TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block057 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block057Part000
    + surrogateDiagTailX0RatChunk001Sub000Block057Part001
    + surrogateDiagTailX0RatChunk001Sub000Block057Part002
    + surrogateDiagTailX0RatChunk001Sub000Block057Part003
    + surrogateDiagTailX0RatChunk001Sub000Block057Part004
    + surrogateDiagTailX0RatChunk001Sub000Block057Part005
    + surrogateDiagTailX0RatChunk001Sub000Block057Part006
    + surrogateDiagTailX0RatChunk001Sub000Block057Part007
    + surrogateDiagTailX0RatChunk001Sub000Block057Part008
    + surrogateDiagTailX0RatChunk001Sub000Block057Part009
    + surrogateDiagTailX0RatChunk001Sub000Block057Part010
    + surrogateDiagTailX0RatChunk001Sub000Block057Part011
    + surrogateDiagTailX0RatChunk001Sub000Block057Part012
    + surrogateDiagTailX0RatChunk001Sub000Block057Part013
    + surrogateDiagTailX0RatChunk001Sub000Block057Part014
    + surrogateDiagTailX0RatChunk001Sub000Block057Part015
    + surrogateDiagTailX0RatChunk001Sub000Block057Part016
    + surrogateDiagTailX0RatChunk001Sub000Block057Part017
    + surrogateDiagTailX0RatChunk001Sub000Block057Part018
    + surrogateDiagTailX0RatChunk001Sub000Block057Part019
    + surrogateDiagTailX0RatChunk001Sub000Block057Part020
    + surrogateDiagTailX0RatChunk001Sub000Block057Part021
    + surrogateDiagTailX0RatChunk001Sub000Block057Part022
    + surrogateDiagTailX0RatChunk001Sub000Block057Part023
    + surrogateDiagTailX0RatChunk001Sub000Block057Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block057_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block057Head + surrogateDiagTailX0RatChunk001Sub000Block057Mid + surrogateDiagTailX0RatChunk001Sub000Block057Tail =
      surrogateDiagTailX0RatChunk001Sub000Block057 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block057Head surrogateDiagTailX0RatChunk001Sub000Block057Mid surrogateDiagTailX0RatChunk001Sub000Block057Tail surrogateDiagTailX0RatChunk001Sub000Block057
  ring

def SurrogateDiagonalTailChunk001Sub000Block057HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block057HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block057Head

def SurrogateDiagonalTailChunk001Sub000Block057MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block057MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block057Mid

def SurrogateDiagonalTailChunk001Sub000Block057TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block057TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block057Tail

theorem surrogateDiagonalTailChunk001Sub000Block057_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block057HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block057MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block057TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block057Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block057 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block057HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block057MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block057TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block057Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block057_eq_head_add_mid_add_tail

/-- Block 058 covers tail-support indices [11450,11475) and q from 18885 to 18922. -/

def TailChunk001Sub000Block058Part000SupportExplicit : Finset ℕ :=
  ([18885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part000 : ℚ :=
  (136165262275 : ℚ) / 1603206218149644288

def SurrogateDiagonalTailChunk001Sub000Block058Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18885
    = surrogateDiagTailX0RatChunk001Sub000Block058Part000

theorem surrogateDiagonalTailChunk001Sub000Block058Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part000] using hcert

def TailChunk001Sub000Block058Part001SupportExplicit : Finset ℕ :=
  ([18886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part001 : ℚ :=
  (11484459611 : ℚ) / 23337052141132800

def SurrogateDiagonalTailChunk001Sub000Block058Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18886
    = surrogateDiagTailX0RatChunk001Sub000Block058Part001

theorem surrogateDiagonalTailChunk001Sub000Block058Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part001] using hcert

def TailChunk001Sub000Block058Part002SupportExplicit : Finset ℕ :=
  ([18887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part002 : ℚ :=
  (16142232239 : ℚ) / 3277455360000000000

def SurrogateDiagonalTailChunk001Sub000Block058Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18887
    = surrogateDiagTailX0RatChunk001Sub000Block058Part002

theorem surrogateDiagonalTailChunk001Sub000Block058Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part002] using hcert

def TailChunk001Sub000Block058Part003SupportExplicit : Finset ℕ :=
  ([18889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part003 : ℚ :=
  (199451088725 : ℚ) / 115236036605103980544

def SurrogateDiagonalTailChunk001Sub000Block058Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18889
    = surrogateDiagTailX0RatChunk001Sub000Block058Part003

theorem surrogateDiagonalTailChunk001Sub000Block058Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part003] using hcert

def TailChunk001Sub000Block058Part004SupportExplicit : Finset ℕ :=
  ([18890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part004 : ℚ :=
  (1337328702975 : ℚ) / 2711149892847271936

def SurrogateDiagonalTailChunk001Sub000Block058Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18890
    = surrogateDiagTailX0RatChunk001Sub000Block058Part004

theorem surrogateDiagonalTailChunk001Sub000Block058Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part004] using hcert

def TailChunk001Sub000Block058Part005SupportExplicit : Finset ℕ :=
  ([18893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part005 : ℚ :=
  (455796671075 : ℚ) / 85855801341980971584

def SurrogateDiagonalTailChunk001Sub000Block058Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18893
    = surrogateDiagTailX0RatChunk001Sub000Block058Part005

theorem surrogateDiagonalTailChunk001Sub000Block058Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part005] using hcert

def TailChunk001Sub000Block058Part006SupportExplicit : Finset ℕ :=
  ([18894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part006 : ℚ :=
  (2948189490325 : ℚ) / 3399021490429052928

def SurrogateDiagonalTailChunk001Sub000Block058Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18894
    = surrogateDiagTailX0RatChunk001Sub000Block058Part006

theorem surrogateDiagonalTailChunk001Sub000Block058Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part006] using hcert

def TailChunk001Sub000Block058Part007SupportExplicit : Finset ℕ :=
  ([18895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part007 : ℚ :=
  (297776988375 : ℚ) / 43470374714002118656

def SurrogateDiagonalTailChunk001Sub000Block058Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18895
    = surrogateDiagTailX0RatChunk001Sub000Block058Part007

theorem surrogateDiagonalTailChunk001Sub000Block058Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part007] using hcert

def TailChunk001Sub000Block058Part008SupportExplicit : Finset ℕ :=
  ([18897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part008 : ℚ :=
  (1239837640025 : ℚ) / 31472226713873753664

def SurrogateDiagonalTailChunk001Sub000Block058Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18897
    = surrogateDiagTailX0RatChunk001Sub000Block058Part008

theorem surrogateDiagonalTailChunk001Sub000Block058Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part008] using hcert

def TailChunk001Sub000Block058Part009SupportExplicit : Finset ℕ :=
  ([18898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part009 : ℚ :=
  (191552539249 : ℚ) / 542045822382979200

def SurrogateDiagonalTailChunk001Sub000Block058Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18898
    = surrogateDiagTailX0RatChunk001Sub000Block058Part009

theorem surrogateDiagonalTailChunk001Sub000Block058Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part009] using hcert

def TailChunk001Sub000Block058Part010SupportExplicit : Finset ℕ :=
  ([18899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block058Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18899
    = surrogateDiagTailX0RatChunk001Sub000Block058Part010

theorem surrogateDiagonalTailChunk001Sub000Block058Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part010] using hcert

def TailChunk001Sub000Block058Part011SupportExplicit : Finset ℕ :=
  ([18901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part011 : ℚ :=
  (3153785621 : ℚ) / 5732289908736000000

def SurrogateDiagonalTailChunk001Sub000Block058Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18901
    = surrogateDiagTailX0RatChunk001Sub000Block058Part011

theorem surrogateDiagonalTailChunk001Sub000Block058Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part011] using hcert

def TailChunk001Sub000Block058Part012SupportExplicit : Finset ℕ :=
  ([18902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part012 : ℚ :=
  (4945833239275 : ℚ) / 14404504575637997568

def SurrogateDiagonalTailChunk001Sub000Block058Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18902
    = surrogateDiagTailX0RatChunk001Sub000Block058Part012

theorem surrogateDiagonalTailChunk001Sub000Block058Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part012] using hcert

def TailChunk001Sub000Block058Part013SupportExplicit : Finset ℕ :=
  ([18903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part013 : ℚ :=
  (35446429 : ℚ) / 900349233840000

def SurrogateDiagonalTailChunk001Sub000Block058Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18903
    = surrogateDiagTailX0RatChunk001Sub000Block058Part013

theorem surrogateDiagonalTailChunk001Sub000Block058Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part013] using hcert

def TailChunk001Sub000Block058Part014SupportExplicit : Finset ℕ :=
  ([18905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part014 : ℚ :=
  (352924880725 : ℚ) / 34426775774245257216

def SurrogateDiagonalTailChunk001Sub000Block058Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18905
    = surrogateDiagTailX0RatChunk001Sub000Block058Part014

theorem surrogateDiagonalTailChunk001Sub000Block058Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part014] using hcert

def TailChunk001Sub000Block058Part015SupportExplicit : Finset ℕ :=
  ([18906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part015 : ℚ :=
  (1445054856125 : ℚ) / 1603109555001360384

def SurrogateDiagonalTailChunk001Sub000Block058Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18906
    = surrogateDiagTailX0RatChunk001Sub000Block058Part015

theorem surrogateDiagonalTailChunk001Sub000Block058Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part015] using hcert

def TailChunk001Sub000Block058Part016SupportExplicit : Finset ℕ :=
  ([18907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part016 : ℚ :=
  (621557353675 : ℚ) / 146275586870039543808

def SurrogateDiagonalTailChunk001Sub000Block058Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18907
    = surrogateDiagTailX0RatChunk001Sub000Block058Part016

theorem surrogateDiagonalTailChunk001Sub000Block058Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part016] using hcert

def TailChunk001Sub000Block058Part017SupportExplicit : Finset ℕ :=
  ([18910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part017 : ℚ :=
  (300083969 : ℚ) / 537584615424000

def SurrogateDiagonalTailChunk001Sub000Block058Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18910
    = surrogateDiagTailX0RatChunk001Sub000Block058Part017

theorem surrogateDiagonalTailChunk001Sub000Block058Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part017] using hcert

def TailChunk001Sub000Block058Part018SupportExplicit : Finset ℕ :=
  ([18911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block058Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18911
    = surrogateDiagTailX0RatChunk001Sub000Block058Part018

theorem surrogateDiagonalTailChunk001Sub000Block058Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part018] using hcert

def TailChunk001Sub000Block058Part019SupportExplicit : Finset ℕ :=
  ([18913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block058Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18913
    = surrogateDiagTailX0RatChunk001Sub000Block058Part019

theorem surrogateDiagonalTailChunk001Sub000Block058Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part019] using hcert

def TailChunk001Sub000Block058Part020SupportExplicit : Finset ℕ :=
  ([18915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part020 : ℚ :=
  (2099709129475 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk001Sub000Block058Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18915
    = surrogateDiagTailX0RatChunk001Sub000Block058Part020

theorem surrogateDiagonalTailChunk001Sub000Block058Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part020] using hcert

def TailChunk001Sub000Block058Part021SupportExplicit : Finset ℕ :=
  ([18917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block058Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18917
    = surrogateDiagTailX0RatChunk001Sub000Block058Part021

theorem surrogateDiagonalTailChunk001Sub000Block058Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part021] using hcert

def TailChunk001Sub000Block058Part022SupportExplicit : Finset ℕ :=
  ([18919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block058Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18919
    = surrogateDiagTailX0RatChunk001Sub000Block058Part022

theorem surrogateDiagonalTailChunk001Sub000Block058Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part022] using hcert

def TailChunk001Sub000Block058Part023SupportExplicit : Finset ℕ :=
  ([18921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part023 : ℚ :=
  (567691715425 : ℚ) / 6211337916820488192

def SurrogateDiagonalTailChunk001Sub000Block058Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18921
    = surrogateDiagTailX0RatChunk001Sub000Block058Part023

theorem surrogateDiagonalTailChunk001Sub000Block058Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part023] using hcert

def TailChunk001Sub000Block058Part024SupportExplicit : Finset ℕ :=
  ([18922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block058Part024 : ℚ :=
  (2237763025 : ℚ) / 8010348219854112

def SurrogateDiagonalTailChunk001Sub000Block058Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18922
    = surrogateDiagTailX0RatChunk001Sub000Block058Part024

theorem surrogateDiagonalTailChunk001Sub000Block058Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block058Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block058Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block058Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block058Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block058Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block058HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block058Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block058Part000
    + surrogateDiagTailX0RatChunk001Sub000Block058Part001
    + surrogateDiagTailX0RatChunk001Sub000Block058Part002
    + surrogateDiagTailX0RatChunk001Sub000Block058Part003
    + surrogateDiagTailX0RatChunk001Sub000Block058Part004
    + surrogateDiagTailX0RatChunk001Sub000Block058Part005
    + surrogateDiagTailX0RatChunk001Sub000Block058Part006
    + surrogateDiagTailX0RatChunk001Sub000Block058Part007
    + surrogateDiagTailX0RatChunk001Sub000Block058Part008
    + surrogateDiagTailX0RatChunk001Sub000Block058Part009

def surrogateDiagonalTailChunk001Sub000Block058MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block058Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block058Part010
    + surrogateDiagTailX0RatChunk001Sub000Block058Part011
    + surrogateDiagTailX0RatChunk001Sub000Block058Part012
    + surrogateDiagTailX0RatChunk001Sub000Block058Part013
    + surrogateDiagTailX0RatChunk001Sub000Block058Part014
    + surrogateDiagTailX0RatChunk001Sub000Block058Part015
    + surrogateDiagTailX0RatChunk001Sub000Block058Part016
    + surrogateDiagTailX0RatChunk001Sub000Block058Part017
    + surrogateDiagTailX0RatChunk001Sub000Block058Part018
    + surrogateDiagTailX0RatChunk001Sub000Block058Part019

def surrogateDiagonalTailChunk001Sub000Block058TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block058Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block058Part020
    + surrogateDiagTailX0RatChunk001Sub000Block058Part021
    + surrogateDiagTailX0RatChunk001Sub000Block058Part022
    + surrogateDiagTailX0RatChunk001Sub000Block058Part023
    + surrogateDiagTailX0RatChunk001Sub000Block058Part024

def surrogateDiagonalTailChunk001Sub000Block058Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block058HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block058MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block058TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block058 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block058Part000
    + surrogateDiagTailX0RatChunk001Sub000Block058Part001
    + surrogateDiagTailX0RatChunk001Sub000Block058Part002
    + surrogateDiagTailX0RatChunk001Sub000Block058Part003
    + surrogateDiagTailX0RatChunk001Sub000Block058Part004
    + surrogateDiagTailX0RatChunk001Sub000Block058Part005
    + surrogateDiagTailX0RatChunk001Sub000Block058Part006
    + surrogateDiagTailX0RatChunk001Sub000Block058Part007
    + surrogateDiagTailX0RatChunk001Sub000Block058Part008
    + surrogateDiagTailX0RatChunk001Sub000Block058Part009
    + surrogateDiagTailX0RatChunk001Sub000Block058Part010
    + surrogateDiagTailX0RatChunk001Sub000Block058Part011
    + surrogateDiagTailX0RatChunk001Sub000Block058Part012
    + surrogateDiagTailX0RatChunk001Sub000Block058Part013
    + surrogateDiagTailX0RatChunk001Sub000Block058Part014
    + surrogateDiagTailX0RatChunk001Sub000Block058Part015
    + surrogateDiagTailX0RatChunk001Sub000Block058Part016
    + surrogateDiagTailX0RatChunk001Sub000Block058Part017
    + surrogateDiagTailX0RatChunk001Sub000Block058Part018
    + surrogateDiagTailX0RatChunk001Sub000Block058Part019
    + surrogateDiagTailX0RatChunk001Sub000Block058Part020
    + surrogateDiagTailX0RatChunk001Sub000Block058Part021
    + surrogateDiagTailX0RatChunk001Sub000Block058Part022
    + surrogateDiagTailX0RatChunk001Sub000Block058Part023
    + surrogateDiagTailX0RatChunk001Sub000Block058Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block058_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block058Head + surrogateDiagTailX0RatChunk001Sub000Block058Mid + surrogateDiagTailX0RatChunk001Sub000Block058Tail =
      surrogateDiagTailX0RatChunk001Sub000Block058 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block058Head surrogateDiagTailX0RatChunk001Sub000Block058Mid surrogateDiagTailX0RatChunk001Sub000Block058Tail surrogateDiagTailX0RatChunk001Sub000Block058
  ring

def SurrogateDiagonalTailChunk001Sub000Block058HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block058HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block058Head

def SurrogateDiagonalTailChunk001Sub000Block058MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block058MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block058Mid

def SurrogateDiagonalTailChunk001Sub000Block058TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block058TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block058Tail

theorem surrogateDiagonalTailChunk001Sub000Block058_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block058HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block058MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block058TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block058Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block058 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block058HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block058MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block058TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block058Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block058_eq_head_add_mid_add_tail

/-- Block 059 covers tail-support indices [11475,11500) and q from 18923 to 18962. -/

def TailChunk001Sub000Block059Part000SupportExplicit : Finset ℕ :=
  ([18923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part000 : ℚ :=
  (21313526575 : ℚ) / 75595494035837809152

def SurrogateDiagonalTailChunk001Sub000Block059Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18923
    = surrogateDiagTailX0RatChunk001Sub000Block059Part000

theorem surrogateDiagonalTailChunk001Sub000Block059Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part000] using hcert

def TailChunk001Sub000Block059Part001SupportExplicit : Finset ℕ :=
  ([18926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part001 : ℚ :=
  (1399193265625 : ℚ) / 5010702779511078642

def SurrogateDiagonalTailChunk001Sub000Block059Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18926
    = surrogateDiagTailX0RatChunk001Sub000Block059Part001

theorem surrogateDiagonalTailChunk001Sub000Block059Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part001] using hcert

def TailChunk001Sub000Block059Part002SupportExplicit : Finset ℕ :=
  ([18929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part002 : ℚ :=
  (259992859075 : ℚ) / 267426753626982077568

def SurrogateDiagonalTailChunk001Sub000Block059Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18929
    = surrogateDiagTailX0RatChunk001Sub000Block059Part002

theorem surrogateDiagonalTailChunk001Sub000Block059Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part002] using hcert

def TailChunk001Sub000Block059Part003SupportExplicit : Finset ℕ :=
  ([18930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part003 : ℚ :=
  (44208957671 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk001Sub000Block059Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18930
    = surrogateDiagTailX0RatChunk001Sub000Block059Part003

theorem surrogateDiagonalTailChunk001Sub000Block059Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part003] using hcert

def TailChunk001Sub000Block059Part004SupportExplicit : Finset ℕ :=
  ([18931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part004 : ℚ :=
  (22304221177 : ℚ) / 8753880986112000000

def SurrogateDiagonalTailChunk001Sub000Block059Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18931
    = surrogateDiagTailX0RatChunk001Sub000Block059Part004

theorem surrogateDiagonalTailChunk001Sub000Block059Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part004] using hcert

def TailChunk001Sub000Block059Part005SupportExplicit : Finset ℕ :=
  ([18933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part005 : ℚ :=
  (9956525119 : ℚ) / 253702221371814720

def SurrogateDiagonalTailChunk001Sub000Block059Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18933
    = surrogateDiagTailX0RatChunk001Sub000Block059Part005

theorem surrogateDiagonalTailChunk001Sub000Block059Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part005] using hcert

def TailChunk001Sub000Block059Part006SupportExplicit : Finset ℕ :=
  ([18934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part006 : ℚ :=
  (1400376390625 : ℚ) / 5019181124112933042

def SurrogateDiagonalTailChunk001Sub000Block059Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18934
    = surrogateDiagTailX0RatChunk001Sub000Block059Part006

theorem surrogateDiagonalTailChunk001Sub000Block059Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part006] using hcert

def TailChunk001Sub000Block059Part007SupportExplicit : Finset ℕ :=
  ([18935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part007 : ℚ :=
  (54247487923 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk001Sub000Block059Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18935
    = surrogateDiagTailX0RatChunk001Sub000Block059Part007

theorem surrogateDiagonalTailChunk001Sub000Block059Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part007] using hcert

def TailChunk001Sub000Block059Part008SupportExplicit : Finset ℕ :=
  ([18937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part008 : ℚ :=
  (36831022875 : ℚ) / 46291165647902916608

def SurrogateDiagonalTailChunk001Sub000Block059Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18937
    = surrogateDiagTailX0RatChunk001Sub000Block059Part008

theorem surrogateDiagonalTailChunk001Sub000Block059Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part008] using hcert

def TailChunk001Sub000Block059Part009SupportExplicit : Finset ℕ :=
  ([18938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part009 : ℚ :=
  (5106498299125 : ℚ) / 15660511970803580928

def SurrogateDiagonalTailChunk001Sub000Block059Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18938
    = surrogateDiagTailX0RatChunk001Sub000Block059Part009

theorem surrogateDiagonalTailChunk001Sub000Block059Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part009] using hcert

def TailChunk001Sub000Block059Part010SupportExplicit : Finset ℕ :=
  ([18939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part010 : ℚ :=
  (34501750575 : ℚ) / 19052897108034328576

def SurrogateDiagonalTailChunk001Sub000Block059Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18939
    = surrogateDiagTailX0RatChunk001Sub000Block059Part010

theorem surrogateDiagonalTailChunk001Sub000Block059Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part010] using hcert

def TailChunk001Sub000Block059Part011SupportExplicit : Finset ℕ :=
  ([18941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part011 : ℚ :=
  (170364965 : ℚ) / 50146072121622528

def SurrogateDiagonalTailChunk001Sub000Block059Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18941
    = surrogateDiagTailX0RatChunk001Sub000Block059Part011

theorem surrogateDiagonalTailChunk001Sub000Block059Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part011] using hcert

def TailChunk001Sub000Block059Part012SupportExplicit : Finset ℕ :=
  ([18942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part012 : ℚ :=
  (71881849849 : ℚ) / 53094776832000000

def SurrogateDiagonalTailChunk001Sub000Block059Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18942
    = surrogateDiagTailX0RatChunk001Sub000Block059Part012

theorem surrogateDiagonalTailChunk001Sub000Block059Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part012] using hcert

def TailChunk001Sub000Block059Part013SupportExplicit : Finset ℕ :=
  ([18943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part013 : ℚ :=
  (78844889575 : ℚ) / 64579435084992287232

def SurrogateDiagonalTailChunk001Sub000Block059Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18943
    = surrogateDiagTailX0RatChunk001Sub000Block059Part013

theorem surrogateDiagonalTailChunk001Sub000Block059Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part013] using hcert

def TailChunk001Sub000Block059Part014SupportExplicit : Finset ℕ :=
  ([18946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part014 : ℚ :=
  (1402152015625 : ℚ) / 5031918809049464832

def SurrogateDiagonalTailChunk001Sub000Block059Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18946
    = surrogateDiagTailX0RatChunk001Sub000Block059Part014

theorem surrogateDiagonalTailChunk001Sub000Block059Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part014] using hcert

def TailChunk001Sub000Block059Part015SupportExplicit : Finset ℕ :=
  ([18947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block059Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18947
    = surrogateDiagTailX0RatChunk001Sub000Block059Part015

theorem surrogateDiagonalTailChunk001Sub000Block059Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part015] using hcert

def TailChunk001Sub000Block059Part016SupportExplicit : Finset ℕ :=
  ([18949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part016 : ℚ :=
  (458498130875 : ℚ) / 86878643992383127104

def SurrogateDiagonalTailChunk001Sub000Block059Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18949
    = surrogateDiagTailX0RatChunk001Sub000Block059Part016

theorem surrogateDiagonalTailChunk001Sub000Block059Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part016] using hcert

def TailChunk001Sub000Block059Part017SupportExplicit : Finset ℕ :=
  ([18951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part017 : ℚ :=
  (125025 : ℚ) / 12730881400997888

def SurrogateDiagonalTailChunk001Sub000Block059Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18951
    = surrogateDiagTailX0RatChunk001Sub000Block059Part017

theorem surrogateDiagonalTailChunk001Sub000Block059Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part017] using hcert

def TailChunk001Sub000Block059Part018SupportExplicit : Finset ℕ :=
  ([18953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part018 : ℚ :=
  (3193690069 : ℚ) / 1256381111785161600

def SurrogateDiagonalTailChunk001Sub000Block059Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18953
    = surrogateDiagTailX0RatChunk001Sub000Block059Part018

theorem surrogateDiagonalTailChunk001Sub000Block059Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part018] using hcert

def TailChunk001Sub000Block059Part019SupportExplicit : Finset ℕ :=
  ([18955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part019 : ℚ :=
  (307207027075 : ℚ) / 16982725980541943808

def SurrogateDiagonalTailChunk001Sub000Block059Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18955
    = surrogateDiagTailX0RatChunk001Sub000Block059Part019

theorem surrogateDiagonalTailChunk001Sub000Block059Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part019] using hcert

def TailChunk001Sub000Block059Part020SupportExplicit : Finset ℕ :=
  ([18957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part020 : ℚ :=
  (983736703 : ℚ) / 576062613228748800

def SurrogateDiagonalTailChunk001Sub000Block059Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18957
    = surrogateDiagTailX0RatChunk001Sub000Block059Part020

theorem surrogateDiagonalTailChunk001Sub000Block059Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part020] using hcert

def TailChunk001Sub000Block059Part021SupportExplicit : Finset ℕ :=
  ([18958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part021 : ℚ :=
  (1403928765625 : ℚ) / 5044680722904111282

def SurrogateDiagonalTailChunk001Sub000Block059Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18958
    = surrogateDiagTailX0RatChunk001Sub000Block059Part021

theorem surrogateDiagonalTailChunk001Sub000Block059Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part021] using hcert

def TailChunk001Sub000Block059Part022SupportExplicit : Finset ℕ :=
  ([18959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block059Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18959
    = surrogateDiagTailX0RatChunk001Sub000Block059Part022

theorem surrogateDiagonalTailChunk001Sub000Block059Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part022] using hcert

def TailChunk001Sub000Block059Part023SupportExplicit : Finset ℕ :=
  ([18961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part023 : ℚ :=
  (6104700775 : ℚ) / 16669651836773491776

def SurrogateDiagonalTailChunk001Sub000Block059Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18961
    = surrogateDiagTailX0RatChunk001Sub000Block059Part023

theorem surrogateDiagonalTailChunk001Sub000Block059Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part023] using hcert

def TailChunk001Sub000Block059Part024SupportExplicit : Finset ℕ :=
  ([18962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block059Part024 : ℚ :=
  (2583982593275 : ℚ) / 8072429385624035904

def SurrogateDiagonalTailChunk001Sub000Block059Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18962
    = surrogateDiagTailX0RatChunk001Sub000Block059Part024

theorem surrogateDiagonalTailChunk001Sub000Block059Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block059Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block059Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block059Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block059Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block059Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block059HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block059Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block059Part000
    + surrogateDiagTailX0RatChunk001Sub000Block059Part001
    + surrogateDiagTailX0RatChunk001Sub000Block059Part002
    + surrogateDiagTailX0RatChunk001Sub000Block059Part003
    + surrogateDiagTailX0RatChunk001Sub000Block059Part004
    + surrogateDiagTailX0RatChunk001Sub000Block059Part005
    + surrogateDiagTailX0RatChunk001Sub000Block059Part006
    + surrogateDiagTailX0RatChunk001Sub000Block059Part007
    + surrogateDiagTailX0RatChunk001Sub000Block059Part008
    + surrogateDiagTailX0RatChunk001Sub000Block059Part009

def surrogateDiagonalTailChunk001Sub000Block059MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block059Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block059Part010
    + surrogateDiagTailX0RatChunk001Sub000Block059Part011
    + surrogateDiagTailX0RatChunk001Sub000Block059Part012
    + surrogateDiagTailX0RatChunk001Sub000Block059Part013
    + surrogateDiagTailX0RatChunk001Sub000Block059Part014
    + surrogateDiagTailX0RatChunk001Sub000Block059Part015
    + surrogateDiagTailX0RatChunk001Sub000Block059Part016
    + surrogateDiagTailX0RatChunk001Sub000Block059Part017
    + surrogateDiagTailX0RatChunk001Sub000Block059Part018
    + surrogateDiagTailX0RatChunk001Sub000Block059Part019

def surrogateDiagonalTailChunk001Sub000Block059TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block059Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block059Part020
    + surrogateDiagTailX0RatChunk001Sub000Block059Part021
    + surrogateDiagTailX0RatChunk001Sub000Block059Part022
    + surrogateDiagTailX0RatChunk001Sub000Block059Part023
    + surrogateDiagTailX0RatChunk001Sub000Block059Part024

def surrogateDiagonalTailChunk001Sub000Block059Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block059HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block059MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block059TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block059 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block059Part000
    + surrogateDiagTailX0RatChunk001Sub000Block059Part001
    + surrogateDiagTailX0RatChunk001Sub000Block059Part002
    + surrogateDiagTailX0RatChunk001Sub000Block059Part003
    + surrogateDiagTailX0RatChunk001Sub000Block059Part004
    + surrogateDiagTailX0RatChunk001Sub000Block059Part005
    + surrogateDiagTailX0RatChunk001Sub000Block059Part006
    + surrogateDiagTailX0RatChunk001Sub000Block059Part007
    + surrogateDiagTailX0RatChunk001Sub000Block059Part008
    + surrogateDiagTailX0RatChunk001Sub000Block059Part009
    + surrogateDiagTailX0RatChunk001Sub000Block059Part010
    + surrogateDiagTailX0RatChunk001Sub000Block059Part011
    + surrogateDiagTailX0RatChunk001Sub000Block059Part012
    + surrogateDiagTailX0RatChunk001Sub000Block059Part013
    + surrogateDiagTailX0RatChunk001Sub000Block059Part014
    + surrogateDiagTailX0RatChunk001Sub000Block059Part015
    + surrogateDiagTailX0RatChunk001Sub000Block059Part016
    + surrogateDiagTailX0RatChunk001Sub000Block059Part017
    + surrogateDiagTailX0RatChunk001Sub000Block059Part018
    + surrogateDiagTailX0RatChunk001Sub000Block059Part019
    + surrogateDiagTailX0RatChunk001Sub000Block059Part020
    + surrogateDiagTailX0RatChunk001Sub000Block059Part021
    + surrogateDiagTailX0RatChunk001Sub000Block059Part022
    + surrogateDiagTailX0RatChunk001Sub000Block059Part023
    + surrogateDiagTailX0RatChunk001Sub000Block059Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block059_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block059Head + surrogateDiagTailX0RatChunk001Sub000Block059Mid + surrogateDiagTailX0RatChunk001Sub000Block059Tail =
      surrogateDiagTailX0RatChunk001Sub000Block059 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block059Head surrogateDiagTailX0RatChunk001Sub000Block059Mid surrogateDiagTailX0RatChunk001Sub000Block059Tail surrogateDiagTailX0RatChunk001Sub000Block059
  ring

def SurrogateDiagonalTailChunk001Sub000Block059HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block059HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block059Head

def SurrogateDiagonalTailChunk001Sub000Block059MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block059MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block059Mid

def SurrogateDiagonalTailChunk001Sub000Block059TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block059TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block059Tail

theorem surrogateDiagonalTailChunk001Sub000Block059_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block059HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block059MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block059TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block059Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block059 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block059HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block059MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block059TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block059Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block059_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

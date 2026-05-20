import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [183,184). -/

/-- Block 183 covers tail-support indices [4575,4600) and q from 7577 to 7617. -/

def TailChunk000Sub000Block183Part000SupportExplicit : Finset ℕ :=
  ([7577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part000 : ℚ :=
  (897045765625 : ℚ) / 2059333723539190272

def SurrogateDiagonalTailChunk000Sub000Block183Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7577
    = surrogateDiagTailX0RatChunk000Sub000Block183Part000

theorem surrogateDiagonalTailChunk000Sub000Block183Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part000] using hcert

def TailChunk000Sub000Block183Part001SupportExplicit : Finset ℕ :=
  ([7579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part001 : ℚ :=
  (55306721381 : ℚ) / 75821996054937600

def SurrogateDiagonalTailChunk000Sub000Block183Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7579
    = surrogateDiagTailX0RatChunk000Sub000Block183Part001

theorem surrogateDiagonalTailChunk000Sub000Block183Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part001] using hcert

def TailChunk000Sub000Block183Part002SupportExplicit : Finset ℕ :=
  ([7582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part002 : ℚ :=
  (547965652025 : ℚ) / 132677546722983936

def SurrogateDiagonalTailChunk000Sub000Block183Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7582
    = surrogateDiagTailX0RatChunk000Sub000Block183Part002

theorem surrogateDiagonalTailChunk000Sub000Block183Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part002] using hcert

def TailChunk000Sub000Block183Part003SupportExplicit : Finset ℕ :=
  ([7583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part003 : ℚ :=
  (898467015625 : ℚ) / 2065865238087141522

def SurrogateDiagonalTailChunk000Sub000Block183Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7583
    = surrogateDiagTailX0RatChunk000Sub000Block183Part003

theorem surrogateDiagonalTailChunk000Sub000Block183Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part003] using hcert

def TailChunk000Sub000Block183Part004SupportExplicit : Finset ℕ :=
  ([7585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part004 : ℚ :=
  (5384518009 : ℚ) / 6116518291046400

def SurrogateDiagonalTailChunk000Sub000Block183Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7585
    = surrogateDiagTailX0RatChunk000Sub000Block183Part004

theorem surrogateDiagonalTailChunk000Sub000Block183Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part004] using hcert

def TailChunk000Sub000Block183Part005SupportExplicit : Finset ℕ :=
  ([7586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part005 : ℚ :=
  (1797996453775 : ℚ) / 517011464570830848

def SurrogateDiagonalTailChunk000Sub000Block183Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7586
    = surrogateDiagTailX0RatChunk000Sub000Block183Part005

theorem surrogateDiagonalTailChunk000Sub000Block183Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part005] using hcert

def TailChunk000Sub000Block183Part006SupportExplicit : Finset ℕ :=
  ([7589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part006 : ℚ :=
  (899889390625 : ℚ) / 2072412277156476192

def SurrogateDiagonalTailChunk000Sub000Block183Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7589
    = surrogateDiagTailX0RatChunk000Sub000Block183Part006

theorem surrogateDiagonalTailChunk000Sub000Block183Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part006] using hcert

def TailChunk000Sub000Block183Part007SupportExplicit : Finset ℕ :=
  ([7590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part007 : ℚ :=
  (6478134079 : ℚ) / 239926119628800

def SurrogateDiagonalTailChunk000Sub000Block183Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7590
    = surrogateDiagTailX0RatChunk000Sub000Block183Part007

theorem surrogateDiagonalTailChunk000Sub000Block183Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part007] using hcert

def TailChunk000Sub000Block183Part008SupportExplicit : Finset ℕ :=
  ([7591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part008 : ℚ :=
  (1440582025 : ℚ) / 3319356924247122

def SurrogateDiagonalTailChunk000Sub000Block183Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7591
    = surrogateDiagTailX0RatChunk000Sub000Block183Part008

theorem surrogateDiagonalTailChunk000Sub000Block183Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part008] using hcert

def TailChunk000Sub000Block183Part009SupportExplicit : Finset ℕ :=
  ([7593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part009 : ℚ :=
  (5003065423 : ℚ) / 4097971511416200

def SurrogateDiagonalTailChunk000Sub000Block183Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7593
    = surrogateDiagTailX0RatChunk000Sub000Block183Part009

theorem surrogateDiagonalTailChunk000Sub000Block183Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part009] using hcert

def TailChunk000Sub000Block183Part010SupportExplicit : Finset ℕ :=
  ([7594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part010 : ℚ :=
  (225268890625 : ℚ) / 129799100421318432

def SurrogateDiagonalTailChunk000Sub000Block183Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7594
    = surrogateDiagTailX0RatChunk000Sub000Block183Part010

theorem surrogateDiagonalTailChunk000Sub000Block183Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part010] using hcert

def TailChunk000Sub000Block183Part011SupportExplicit : Finset ℕ :=
  ([7597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part011 : ℚ :=
  (6990759161 : ℚ) / 15159067111980960

def SurrogateDiagonalTailChunk000Sub000Block183Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7597
    = surrogateDiagTailX0RatChunk000Sub000Block183Part011

theorem surrogateDiagonalTailChunk000Sub000Block183Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part011] using hcert

def TailChunk000Sub000Block183Part012SupportExplicit : Finset ℕ :=
  ([7598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part012 : ℚ :=
  (350407171 : ℚ) / 175587010540032

def SurrogateDiagonalTailChunk000Sub000Block183Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7598
    = surrogateDiagTailX0RatChunk000Sub000Block183Part012

theorem surrogateDiagonalTailChunk000Sub000Block183Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part012] using hcert

def TailChunk000Sub000Block183Part013SupportExplicit : Finset ℕ :=
  ([7599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part013 : ℚ :=
  (307898334675 : ℚ) / 209663283710394368

def SurrogateDiagonalTailChunk000Sub000Block183Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7599
    = surrogateDiagTailX0RatChunk000Sub000Block183Part013

theorem surrogateDiagonalTailChunk000Sub000Block183Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part013] using hcert

def TailChunk000Sub000Block183Part014SupportExplicit : Finset ℕ :=
  ([7601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part014 : ℚ :=
  (4210426649 : ℚ) / 7557218141400000

def SurrogateDiagonalTailChunk000Sub000Block183Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7601
    = surrogateDiagTailX0RatChunk000Sub000Block183Part014

theorem surrogateDiagonalTailChunk000Sub000Block183Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part014] using hcert

def TailChunk000Sub000Block183Part015SupportExplicit : Finset ℕ :=
  ([7602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part015 : ℚ :=
  (914659597 : ℚ) / 80637692313600

def SurrogateDiagonalTailChunk000Sub000Block183Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7602
    = surrogateDiagTailX0RatChunk000Sub000Block183Part015

theorem surrogateDiagonalTailChunk000Sub000Block183Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part015] using hcert

def TailChunk000Sub000Block183Part016SupportExplicit : Finset ℕ :=
  ([7603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part016 : ℚ :=
  (903212640625 : ℚ) / 2087749212901320402

def SurrogateDiagonalTailChunk000Sub000Block183Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7603
    = surrogateDiagTailX0RatChunk000Sub000Block183Part016

theorem surrogateDiagonalTailChunk000Sub000Block183Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part016] using hcert

def TailChunk000Sub000Block183Part017SupportExplicit : Finset ℕ :=
  ([7606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part017 : ℚ :=
  (225981390625 : ℚ) / 130621695791345202

def SurrogateDiagonalTailChunk000Sub000Block183Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7606
    = surrogateDiagTailX0RatChunk000Sub000Block183Part017

theorem surrogateDiagonalTailChunk000Sub000Block183Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part017] using hcert

def TailChunk000Sub000Block183Part018SupportExplicit : Finset ℕ :=
  ([7607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part018 : ℚ :=
  (904163265625 : ℚ) / 2092146787393150962

def SurrogateDiagonalTailChunk000Sub000Block183Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7607
    = surrogateDiagTailX0RatChunk000Sub000Block183Part018

theorem surrogateDiagonalTailChunk000Sub000Block183Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part018] using hcert

def TailChunk000Sub000Block183Part019SupportExplicit : Finset ℕ :=
  ([7609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part019 : ℚ :=
  (2950892768275 : ℚ) / 4507660108155120768

def SurrogateDiagonalTailChunk000Sub000Block183Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7609
    = surrogateDiagTailX0RatChunk000Sub000Block183Part019

theorem surrogateDiagonalTailChunk000Sub000Block183Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part019] using hcert

def TailChunk000Sub000Block183Part020SupportExplicit : Finset ℕ :=
  ([7610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part020 : ℚ :=
  (2025317979 : ℚ) / 569495013294080

def SurrogateDiagonalTailChunk000Sub000Block183Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7610
    = surrogateDiagTailX0RatChunk000Sub000Block183Part020

theorem surrogateDiagonalTailChunk000Sub000Block183Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part020] using hcert

def TailChunk000Sub000Block183Part021SupportExplicit : Finset ℕ :=
  ([7611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part021 : ℚ :=
  (119729624425 : ℚ) / 88051345090708608

def SurrogateDiagonalTailChunk000Sub000Block183Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7611
    = surrogateDiagTailX0RatChunk000Sub000Block183Part021

theorem surrogateDiagonalTailChunk000Sub000Block183Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part021] using hcert

def TailChunk000Sub000Block183Part022SupportExplicit : Finset ℕ :=
  ([7613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part022 : ℚ :=
  (54899969 : ℚ) / 112268554180992

def SurrogateDiagonalTailChunk000Sub000Block183Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7613
    = surrogateDiagTailX0RatChunk000Sub000Block183Part022

theorem surrogateDiagonalTailChunk000Sub000Block183Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part022] using hcert

def TailChunk000Sub000Block183Part023SupportExplicit : Finset ℕ :=
  ([7615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part023 : ℚ :=
  (869233387275 : ℚ) / 1144996552934496256

def SurrogateDiagonalTailChunk000Sub000Block183Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7615
    = surrogateDiagTailX0RatChunk000Sub000Block183Part023

theorem surrogateDiagonalTailChunk000Sub000Block183Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part023] using hcert

def TailChunk000Sub000Block183Part024SupportExplicit : Finset ℕ :=
  ([7617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part024 : ℚ :=
  (251737274525 : ℚ) / 207502496226485136

def SurrogateDiagonalTailChunk000Sub000Block183Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7617
    = surrogateDiagTailX0RatChunk000Sub000Block183Part024

theorem surrogateDiagonalTailChunk000Sub000Block183Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block183HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block183Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part000
    + surrogateDiagTailX0RatChunk000Sub000Block183Part001
    + surrogateDiagTailX0RatChunk000Sub000Block183Part002
    + surrogateDiagTailX0RatChunk000Sub000Block183Part003
    + surrogateDiagTailX0RatChunk000Sub000Block183Part004
    + surrogateDiagTailX0RatChunk000Sub000Block183Part005
    + surrogateDiagTailX0RatChunk000Sub000Block183Part006
    + surrogateDiagTailX0RatChunk000Sub000Block183Part007
    + surrogateDiagTailX0RatChunk000Sub000Block183Part008
    + surrogateDiagTailX0RatChunk000Sub000Block183Part009

def surrogateDiagonalTailChunk000Sub000Block183MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block183Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part010
    + surrogateDiagTailX0RatChunk000Sub000Block183Part011
    + surrogateDiagTailX0RatChunk000Sub000Block183Part012
    + surrogateDiagTailX0RatChunk000Sub000Block183Part013
    + surrogateDiagTailX0RatChunk000Sub000Block183Part014
    + surrogateDiagTailX0RatChunk000Sub000Block183Part015
    + surrogateDiagTailX0RatChunk000Sub000Block183Part016
    + surrogateDiagTailX0RatChunk000Sub000Block183Part017
    + surrogateDiagTailX0RatChunk000Sub000Block183Part018
    + surrogateDiagTailX0RatChunk000Sub000Block183Part019

def surrogateDiagonalTailChunk000Sub000Block183TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block183Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part020
    + surrogateDiagTailX0RatChunk000Sub000Block183Part021
    + surrogateDiagTailX0RatChunk000Sub000Block183Part022
    + surrogateDiagTailX0RatChunk000Sub000Block183Part023
    + surrogateDiagTailX0RatChunk000Sub000Block183Part024

def surrogateDiagonalTailChunk000Sub000Block183Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block183HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block183MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block183TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block183 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part000
    + surrogateDiagTailX0RatChunk000Sub000Block183Part001
    + surrogateDiagTailX0RatChunk000Sub000Block183Part002
    + surrogateDiagTailX0RatChunk000Sub000Block183Part003
    + surrogateDiagTailX0RatChunk000Sub000Block183Part004
    + surrogateDiagTailX0RatChunk000Sub000Block183Part005
    + surrogateDiagTailX0RatChunk000Sub000Block183Part006
    + surrogateDiagTailX0RatChunk000Sub000Block183Part007
    + surrogateDiagTailX0RatChunk000Sub000Block183Part008
    + surrogateDiagTailX0RatChunk000Sub000Block183Part009
    + surrogateDiagTailX0RatChunk000Sub000Block183Part010
    + surrogateDiagTailX0RatChunk000Sub000Block183Part011
    + surrogateDiagTailX0RatChunk000Sub000Block183Part012
    + surrogateDiagTailX0RatChunk000Sub000Block183Part013
    + surrogateDiagTailX0RatChunk000Sub000Block183Part014
    + surrogateDiagTailX0RatChunk000Sub000Block183Part015
    + surrogateDiagTailX0RatChunk000Sub000Block183Part016
    + surrogateDiagTailX0RatChunk000Sub000Block183Part017
    + surrogateDiagTailX0RatChunk000Sub000Block183Part018
    + surrogateDiagTailX0RatChunk000Sub000Block183Part019
    + surrogateDiagTailX0RatChunk000Sub000Block183Part020
    + surrogateDiagTailX0RatChunk000Sub000Block183Part021
    + surrogateDiagTailX0RatChunk000Sub000Block183Part022
    + surrogateDiagTailX0RatChunk000Sub000Block183Part023
    + surrogateDiagTailX0RatChunk000Sub000Block183Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block183_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block183Head + surrogateDiagTailX0RatChunk000Sub000Block183Mid + surrogateDiagTailX0RatChunk000Sub000Block183Tail =
      surrogateDiagTailX0RatChunk000Sub000Block183 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block183Head surrogateDiagTailX0RatChunk000Sub000Block183Mid surrogateDiagTailX0RatChunk000Sub000Block183Tail surrogateDiagTailX0RatChunk000Sub000Block183
  ring

def SurrogateDiagonalTailChunk000Sub000Block183HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block183HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block183Head

def SurrogateDiagonalTailChunk000Sub000Block183MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block183MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block183Mid

def SurrogateDiagonalTailChunk000Sub000Block183TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block183TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block183Tail

theorem surrogateDiagonalTailChunk000Sub000Block183_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block183HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block183MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block183TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block183Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block183 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block183HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block183MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block183TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block183Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block183_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

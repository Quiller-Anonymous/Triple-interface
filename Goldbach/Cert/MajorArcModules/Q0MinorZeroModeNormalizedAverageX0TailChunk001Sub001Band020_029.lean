import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [20,30). -/

/-- Block 020 covers tail-support indices [15500,15525) and q from 25554 to 25591. -/

def TailChunk001Sub001Block020Part000SupportExplicit : Finset ℕ :=
  ([25554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part000 : ℚ :=
  (566892665525 : ℚ) / 6575661888565752384

def SurrogateDiagonalTailChunk001Sub001Block020Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25554
    = surrogateDiagTailX0RatChunk001Sub001Block020Part000

theorem surrogateDiagonalTailChunk001Sub001Block020Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part000] using hcert

def TailChunk001Sub001Block020Part001SupportExplicit : Finset ℕ :=
  ([25555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part001 : ℚ :=
  (608957054125 : ℚ) / 115551281420239896576

def SurrogateDiagonalTailChunk001Sub001Block020Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25555
    = surrogateDiagTailX0RatChunk001Sub001Block020Part001

theorem surrogateDiagonalTailChunk001Sub001Block020Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part001] using hcert

def TailChunk001Sub001Block020Part002SupportExplicit : Finset ℕ :=
  ([25557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part002 : ℚ :=
  (115605526475 : ℚ) / 3149079625510944768

def SurrogateDiagonalTailChunk001Sub001Block020Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25557
    = surrogateDiagTailX0RatChunk001Sub001Block020Part002

theorem surrogateDiagonalTailChunk001Sub001Block020Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part002] using hcert

def TailChunk001Sub001Block020Part003SupportExplicit : Finset ℕ :=
  ([25558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part003 : ℚ :=
  (304863001375 : ℚ) / 48216734497051527168

def SurrogateDiagonalTailChunk001Sub001Block020Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25558
    = surrogateDiagTailX0RatChunk001Sub001Block020Part003

theorem surrogateDiagonalTailChunk001Sub001Block020Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part003] using hcert

def TailChunk001Sub001Block020Part004SupportExplicit : Finset ℕ :=
  ([25559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part004 : ℚ :=
  (5980540477 : ℚ) / 39572818105120819200

def SurrogateDiagonalTailChunk001Sub001Block020Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25559
    = surrogateDiagTailX0RatChunk001Sub001Block020Part004

theorem surrogateDiagonalTailChunk001Sub001Block020Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part004] using hcert

def TailChunk001Sub001Block020Part005SupportExplicit : Finset ℕ :=
  ([25561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block020Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25561
    = surrogateDiagTailX0RatChunk001Sub001Block020Part005

theorem surrogateDiagonalTailChunk001Sub001Block020Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part005] using hcert

def TailChunk001Sub001Block020Part006SupportExplicit : Finset ℕ :=
  ([25562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block020Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25562
    = surrogateDiagTailX0RatChunk001Sub001Block020Part006

theorem surrogateDiagonalTailChunk001Sub001Block020Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part006] using hcert

def TailChunk001Sub001Block020Part007SupportExplicit : Finset ℕ :=
  ([25563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part007 : ℚ :=
  (9075049949 : ℚ) / 421633603631554560

def SurrogateDiagonalTailChunk001Sub001Block020Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25563
    = surrogateDiagTailX0RatChunk001Sub001Block020Part007

theorem surrogateDiagonalTailChunk001Sub001Block020Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part007] using hcert

def TailChunk001Sub001Block020Part008SupportExplicit : Finset ℕ :=
  ([25565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part008 : ℚ :=
  (1634534548375 : ℚ) / 437149720245195767808

def SurrogateDiagonalTailChunk001Sub001Block020Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25565
    = surrogateDiagTailX0RatChunk001Sub001Block020Part008

theorem surrogateDiagonalTailChunk001Sub001Block020Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part008] using hcert

def TailChunk001Sub001Block020Part009SupportExplicit : Finset ℕ :=
  ([25566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part009 : ℚ :=
  (1134850081 : ℚ) / 13176050113486080

def SurrogateDiagonalTailChunk001Sub001Block020Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25566
    = surrogateDiagTailX0RatChunk001Sub001Block020Part009

theorem surrogateDiagonalTailChunk001Sub001Block020Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part009] using hcert

def TailChunk001Sub001Block020Part010SupportExplicit : Finset ℕ :=
  ([25567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part010 : ℚ :=
  (8771384479 : ℚ) / 38079673517357107200

def SurrogateDiagonalTailChunk001Sub001Block020Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25567
    = surrogateDiagTailX0RatChunk001Sub001Block020Part010

theorem surrogateDiagonalTailChunk001Sub001Block020Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part010] using hcert

def TailChunk001Sub001Block020Part011SupportExplicit : Finset ℕ :=
  ([25570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part011 : ℚ :=
  (3839103425 : ℚ) / 128271631527346176

def SurrogateDiagonalTailChunk001Sub001Block020Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25570
    = surrogateDiagTailX0RatChunk001Sub001Block020Part011

theorem surrogateDiagonalTailChunk001Sub001Block020Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part011] using hcert

def TailChunk001Sub001Block020Part012SupportExplicit : Finset ℕ :=
  ([25571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part012 : ℚ :=
  (74199581161 : ℚ) / 16521480468902707200

def SurrogateDiagonalTailChunk001Sub001Block020Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25571
    = surrogateDiagTailX0RatChunk001Sub001Block020Part012

theorem surrogateDiagonalTailChunk001Sub001Block020Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part012] using hcert

def TailChunk001Sub001Block020Part013SupportExplicit : Finset ℕ :=
  ([25573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part013 : ℚ :=
  (103850988025 : ℚ) / 1012880355407809408128

def SurrogateDiagonalTailChunk001Sub001Block020Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25573
    = surrogateDiagTailX0RatChunk001Sub001Block020Part013

theorem surrogateDiagonalTailChunk001Sub001Block020Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part013] using hcert

def TailChunk001Sub001Block020Part014SupportExplicit : Finset ℕ :=
  ([25574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part014 : ℚ :=
  (231097852675 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub001Block020Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25574
    = surrogateDiagTailX0RatChunk001Sub001Block020Part014

theorem surrogateDiagonalTailChunk001Sub001Block020Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part014] using hcert

def TailChunk001Sub001Block020Part015SupportExplicit : Finset ℕ :=
  ([25577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block020Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25577
    = surrogateDiagTailX0RatChunk001Sub001Block020Part015

theorem surrogateDiagonalTailChunk001Sub001Block020Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part015] using hcert

def TailChunk001Sub001Block020Part016SupportExplicit : Finset ℕ :=
  ([25579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block020Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25579
    = surrogateDiagTailX0RatChunk001Sub001Block020Part016

theorem surrogateDiagonalTailChunk001Sub001Block020Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part016] using hcert

def TailChunk001Sub001Block020Part017SupportExplicit : Finset ℕ :=
  ([25581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part017 : ℚ :=
  (324565516025 : ℚ) / 15100805683056526272

def SurrogateDiagonalTailChunk001Sub001Block020Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25581
    = surrogateDiagTailX0RatChunk001Sub001Block020Part017

theorem surrogateDiagonalTailChunk001Sub001Block020Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part017] using hcert

def TailChunk001Sub001Block020Part018SupportExplicit : Finset ℕ :=
  ([25582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block020Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25582
    = surrogateDiagTailX0RatChunk001Sub001Block020Part018

theorem surrogateDiagonalTailChunk001Sub001Block020Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part018] using hcert

def TailChunk001Sub001Block020Part019SupportExplicit : Finset ℕ :=
  ([25583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block020Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25583
    = surrogateDiagTailX0RatChunk001Sub001Block020Part019

theorem surrogateDiagonalTailChunk001Sub001Block020Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part019] using hcert

def TailChunk001Sub001Block020Part020SupportExplicit : Finset ℕ :=
  ([25585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part020 : ℚ :=
  (115512442975 : ℚ) / 8056188571503034368

def SurrogateDiagonalTailChunk001Sub001Block020Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25585
    = surrogateDiagTailX0RatChunk001Sub001Block020Part020

theorem surrogateDiagonalTailChunk001Sub001Block020Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part020] using hcert

def TailChunk001Sub001Block020Part021SupportExplicit : Finset ℕ :=
  ([25586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part021 : ℚ :=
  (4093885 : ℚ) / 439403250917568

def SurrogateDiagonalTailChunk001Sub001Block020Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25586
    = surrogateDiagTailX0RatChunk001Sub001Block020Part021

theorem surrogateDiagonalTailChunk001Sub001Block020Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part021] using hcert

def TailChunk001Sub001Block020Part022SupportExplicit : Finset ℕ :=
  ([25589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block020Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25589
    = surrogateDiagTailX0RatChunk001Sub001Block020Part022

theorem surrogateDiagonalTailChunk001Sub001Block020Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part022] using hcert

def TailChunk001Sub001Block020Part023SupportExplicit : Finset ℕ :=
  ([25590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part023 : ℚ :=
  (1227480616975 : ℚ) / 5396910126483898368

def SurrogateDiagonalTailChunk001Sub001Block020Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25590
    = surrogateDiagTailX0RatChunk001Sub001Block020Part023

theorem surrogateDiagonalTailChunk001Sub001Block020Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part023] using hcert

def TailChunk001Sub001Block020Part024SupportExplicit : Finset ℕ :=
  ([25591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block020Part024 : ℚ :=
  (11058474275 : ℚ) / 113329455202777761792

def SurrogateDiagonalTailChunk001Sub001Block020Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25591
    = surrogateDiagTailX0RatChunk001Sub001Block020Part024

theorem surrogateDiagonalTailChunk001Sub001Block020Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block020Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block020Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block020Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block020Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block020Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block020HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block020Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block020Part000
    + surrogateDiagTailX0RatChunk001Sub001Block020Part001
    + surrogateDiagTailX0RatChunk001Sub001Block020Part002
    + surrogateDiagTailX0RatChunk001Sub001Block020Part003
    + surrogateDiagTailX0RatChunk001Sub001Block020Part004
    + surrogateDiagTailX0RatChunk001Sub001Block020Part005
    + surrogateDiagTailX0RatChunk001Sub001Block020Part006
    + surrogateDiagTailX0RatChunk001Sub001Block020Part007
    + surrogateDiagTailX0RatChunk001Sub001Block020Part008
    + surrogateDiagTailX0RatChunk001Sub001Block020Part009

def surrogateDiagonalTailChunk001Sub001Block020MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block020Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block020Part010
    + surrogateDiagTailX0RatChunk001Sub001Block020Part011
    + surrogateDiagTailX0RatChunk001Sub001Block020Part012
    + surrogateDiagTailX0RatChunk001Sub001Block020Part013
    + surrogateDiagTailX0RatChunk001Sub001Block020Part014
    + surrogateDiagTailX0RatChunk001Sub001Block020Part015
    + surrogateDiagTailX0RatChunk001Sub001Block020Part016
    + surrogateDiagTailX0RatChunk001Sub001Block020Part017
    + surrogateDiagTailX0RatChunk001Sub001Block020Part018
    + surrogateDiagTailX0RatChunk001Sub001Block020Part019

def surrogateDiagonalTailChunk001Sub001Block020TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block020Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block020Part020
    + surrogateDiagTailX0RatChunk001Sub001Block020Part021
    + surrogateDiagTailX0RatChunk001Sub001Block020Part022
    + surrogateDiagTailX0RatChunk001Sub001Block020Part023
    + surrogateDiagTailX0RatChunk001Sub001Block020Part024

def surrogateDiagonalTailChunk001Sub001Block020Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block020HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block020MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block020TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block020 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block020Part000
    + surrogateDiagTailX0RatChunk001Sub001Block020Part001
    + surrogateDiagTailX0RatChunk001Sub001Block020Part002
    + surrogateDiagTailX0RatChunk001Sub001Block020Part003
    + surrogateDiagTailX0RatChunk001Sub001Block020Part004
    + surrogateDiagTailX0RatChunk001Sub001Block020Part005
    + surrogateDiagTailX0RatChunk001Sub001Block020Part006
    + surrogateDiagTailX0RatChunk001Sub001Block020Part007
    + surrogateDiagTailX0RatChunk001Sub001Block020Part008
    + surrogateDiagTailX0RatChunk001Sub001Block020Part009
    + surrogateDiagTailX0RatChunk001Sub001Block020Part010
    + surrogateDiagTailX0RatChunk001Sub001Block020Part011
    + surrogateDiagTailX0RatChunk001Sub001Block020Part012
    + surrogateDiagTailX0RatChunk001Sub001Block020Part013
    + surrogateDiagTailX0RatChunk001Sub001Block020Part014
    + surrogateDiagTailX0RatChunk001Sub001Block020Part015
    + surrogateDiagTailX0RatChunk001Sub001Block020Part016
    + surrogateDiagTailX0RatChunk001Sub001Block020Part017
    + surrogateDiagTailX0RatChunk001Sub001Block020Part018
    + surrogateDiagTailX0RatChunk001Sub001Block020Part019
    + surrogateDiagTailX0RatChunk001Sub001Block020Part020
    + surrogateDiagTailX0RatChunk001Sub001Block020Part021
    + surrogateDiagTailX0RatChunk001Sub001Block020Part022
    + surrogateDiagTailX0RatChunk001Sub001Block020Part023
    + surrogateDiagTailX0RatChunk001Sub001Block020Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block020_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block020Head + surrogateDiagTailX0RatChunk001Sub001Block020Mid + surrogateDiagTailX0RatChunk001Sub001Block020Tail =
      surrogateDiagTailX0RatChunk001Sub001Block020 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block020Head surrogateDiagTailX0RatChunk001Sub001Block020Mid surrogateDiagTailX0RatChunk001Sub001Block020Tail surrogateDiagTailX0RatChunk001Sub001Block020
  ring

def SurrogateDiagonalTailChunk001Sub001Block020HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block020HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block020Head

def SurrogateDiagonalTailChunk001Sub001Block020MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block020MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block020Mid

def SurrogateDiagonalTailChunk001Sub001Block020TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block020TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block020Tail

theorem surrogateDiagonalTailChunk001Sub001Block020_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block020HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block020MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block020TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block020Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block020 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block020HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block020MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block020TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block020Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block020_eq_head_add_mid_add_tail

/-- Block 021 covers tail-support indices [15525,15550) and q from 25593 to 25633. -/

def TailChunk001Sub001Block021Part000SupportExplicit : Finset ℕ :=
  ([25593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part000 : ℚ :=
  (1078491338275 : ℚ) / 42294990000390930432

def SurrogateDiagonalTailChunk001Sub001Block021Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25593
    = surrogateDiagTailX0RatChunk001Sub001Block021Part000

theorem surrogateDiagonalTailChunk001Sub001Block021Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part000] using hcert

def TailChunk001Sub001Block021Part001SupportExplicit : Finset ℕ :=
  ([25594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part001 : ℚ :=
  (63273701 : ℚ) / 49466022631401024

def SurrogateDiagonalTailChunk001Sub001Block021Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25594
    = surrogateDiagTailX0RatChunk001Sub001Block021Part001

theorem surrogateDiagonalTailChunk001Sub001Block021Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part001] using hcert

def TailChunk001Sub001Block021Part002SupportExplicit : Finset ℕ :=
  ([25595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part002 : ℚ :=
  (1638370797625 : ℚ) / 439205682463154915328

def SurrogateDiagonalTailChunk001Sub001Block021Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25595
    = surrogateDiagTailX0RatChunk001Sub001Block021Part002

theorem surrogateDiagonalTailChunk001Sub001Block021Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part002] using hcert

def TailChunk001Sub001Block021Part003SupportExplicit : Finset ℕ :=
  ([25597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part003 : ℚ :=
  (20401735199 : ℚ) / 6940177674655334400

def SurrogateDiagonalTailChunk001Sub001Block021Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25597
    = surrogateDiagTailX0RatChunk001Sub001Block021Part003

theorem surrogateDiagonalTailChunk001Sub001Block021Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part003] using hcert

def TailChunk001Sub001Block021Part004SupportExplicit : Finset ℕ :=
  ([25598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block021Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25598
    = surrogateDiagTailX0RatChunk001Sub001Block021Part004

theorem surrogateDiagonalTailChunk001Sub001Block021Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part004] using hcert

def TailChunk001Sub001Block021Part005SupportExplicit : Finset ℕ :=
  ([25599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part005 : ℚ :=
  (145876127125 : ℚ) / 3289214353304715264

def SurrogateDiagonalTailChunk001Sub001Block021Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25599
    = surrogateDiagTailX0RatChunk001Sub001Block021Part005

theorem surrogateDiagonalTailChunk001Sub001Block021Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part005] using hcert

def TailChunk001Sub001Block021Part006SupportExplicit : Finset ℕ :=
  ([25601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block021Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25601
    = surrogateDiagTailX0RatChunk001Sub001Block021Part006

theorem surrogateDiagonalTailChunk001Sub001Block021Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part006] using hcert

def TailChunk001Sub001Block021Part007SupportExplicit : Finset ℕ :=
  ([25602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part007 : ℚ :=
  (46025265697 : ℚ) / 409681920000000000

def SurrogateDiagonalTailChunk001Sub001Block021Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25602
    = surrogateDiagTailX0RatChunk001Sub001Block021Part007

theorem surrogateDiagonalTailChunk001Sub001Block021Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part007] using hcert

def TailChunk001Sub001Block021Part008SupportExplicit : Finset ℕ :=
  ([25603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block021Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25603
    = surrogateDiagTailX0RatChunk001Sub001Block021Part008

theorem surrogateDiagonalTailChunk001Sub001Block021Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part008] using hcert

def TailChunk001Sub001Block021Part009SupportExplicit : Finset ℕ :=
  ([25606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part009 : ℚ :=
  (5831592599 : ℚ) / 237639615238563840

def SurrogateDiagonalTailChunk001Sub001Block021Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25606
    = surrogateDiagTailX0RatChunk001Sub001Block021Part009

theorem surrogateDiagonalTailChunk001Sub001Block021Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part009] using hcert

def TailChunk001Sub001Block021Part010SupportExplicit : Finset ℕ :=
  ([25607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part010 : ℚ :=
  (62909724025 : ℚ) / 232526970528834949632

def SurrogateDiagonalTailChunk001Sub001Block021Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25607
    = surrogateDiagTailX0RatChunk001Sub001Block021Part010

theorem surrogateDiagonalTailChunk001Sub001Block021Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part010] using hcert

def TailChunk001Sub001Block021Part011SupportExplicit : Finset ℕ :=
  ([25609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block021Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25609
    = surrogateDiagTailX0RatChunk001Sub001Block021Part011

theorem surrogateDiagonalTailChunk001Sub001Block021Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part011] using hcert

def TailChunk001Sub001Block021Part012SupportExplicit : Finset ℕ :=
  ([25610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part012 : ℚ :=
  (313879185425 : ℚ) / 6529724214952329216

def SurrogateDiagonalTailChunk001Sub001Block021Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25610
    = surrogateDiagTailX0RatChunk001Sub001Block021Part012

theorem surrogateDiagonalTailChunk001Sub001Block021Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part012] using hcert

def TailChunk001Sub001Block021Part013SupportExplicit : Finset ℕ :=
  ([25611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part013 : ℚ :=
  (1138645243525 : ℚ) / 53101217159644127232

def SurrogateDiagonalTailChunk001Sub001Block021Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25611
    = surrogateDiagTailX0RatChunk001Sub001Block021Part013

theorem surrogateDiagonalTailChunk001Sub001Block021Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part013] using hcert

def TailChunk001Sub001Block021Part014SupportExplicit : Finset ℕ :=
  ([25613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part014 : ℚ :=
  (837080423075 : ℚ) / 290119332326271971904

def SurrogateDiagonalTailChunk001Sub001Block021Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25613
    = surrogateDiagTailX0RatChunk001Sub001Block021Part014

theorem surrogateDiagonalTailChunk001Sub001Block021Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part014] using hcert

def TailChunk001Sub001Block021Part015SupportExplicit : Finset ℕ :=
  ([25615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part015 : ℚ :=
  (75242637125 : ℚ) / 16953732905118990336

def SurrogateDiagonalTailChunk001Sub001Block021Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25615
    = surrogateDiagTailX0RatChunk001Sub001Block021Part015

theorem surrogateDiagonalTailChunk001Sub001Block021Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part015] using hcert

def TailChunk001Sub001Block021Part016SupportExplicit : Finset ℕ :=
  ([25617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part016 : ℚ :=
  (2278357612025 : ℚ) / 106302002984029652544

def SurrogateDiagonalTailChunk001Sub001Block021Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25617
    = surrogateDiagTailX0RatChunk001Sub001Block021Part016

theorem surrogateDiagonalTailChunk001Sub001Block021Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part016] using hcert

def TailChunk001Sub001Block021Part017SupportExplicit : Finset ℕ :=
  ([25618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block021Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25618
    = surrogateDiagTailX0RatChunk001Sub001Block021Part017

theorem surrogateDiagonalTailChunk001Sub001Block021Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part017] using hcert

def TailChunk001Sub001Block021Part018SupportExplicit : Finset ℕ :=
  ([25619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part018 : ℚ :=
  (760193721 : ℚ) / 373741362002001920

def SurrogateDiagonalTailChunk001Sub001Block021Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25619
    = surrogateDiagTailX0RatChunk001Sub001Block021Part018

theorem surrogateDiagonalTailChunk001Sub001Block021Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part018] using hcert

def TailChunk001Sub001Block021Part019SupportExplicit : Finset ℕ :=
  ([25621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block021Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25621
    = surrogateDiagTailX0RatChunk001Sub001Block021Part019

theorem surrogateDiagonalTailChunk001Sub001Block021Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part019] using hcert

def TailChunk001Sub001Block021Part020SupportExplicit : Finset ℕ :=
  ([25622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part020 : ℚ :=
  (180474962725 : ℚ) / 55977918887825983488

def SurrogateDiagonalTailChunk001Sub001Block021Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25622
    = surrogateDiagTailX0RatChunk001Sub001Block021Part020

theorem surrogateDiagonalTailChunk001Sub001Block021Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part020] using hcert

def TailChunk001Sub001Block021Part021SupportExplicit : Finset ℕ :=
  ([25626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part021 : ℚ :=
  (93076027 : ℚ) / 1085731037186880

def SurrogateDiagonalTailChunk001Sub001Block021Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25626
    = surrogateDiagTailX0RatChunk001Sub001Block021Part021

theorem surrogateDiagonalTailChunk001Sub001Block021Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part021] using hcert

def TailChunk001Sub001Block021Part022SupportExplicit : Finset ℕ :=
  ([25629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part022 : ℚ :=
  (2280492611975 : ℚ) / 106501350332938334784

def SurrogateDiagonalTailChunk001Sub001Block021Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25629
    = surrogateDiagTailX0RatChunk001Sub001Block021Part022

theorem surrogateDiagonalTailChunk001Sub001Block021Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part022] using hcert

def TailChunk001Sub001Block021Part023SupportExplicit : Finset ℕ :=
  ([25630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part023 : ℚ :=
  (254489241 : ℚ) / 4945241396215808

def SurrogateDiagonalTailChunk001Sub001Block021Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25630
    = surrogateDiagTailX0RatChunk001Sub001Block021Part023

theorem surrogateDiagonalTailChunk001Sub001Block021Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part023] using hcert

def TailChunk001Sub001Block021Part024SupportExplicit : Finset ℕ :=
  ([25633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block021Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block021Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25633
    = surrogateDiagTailX0RatChunk001Sub001Block021Part024

theorem surrogateDiagonalTailChunk001Sub001Block021Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block021Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block021Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block021Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block021Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block021Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block021HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block021Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block021Part000
    + surrogateDiagTailX0RatChunk001Sub001Block021Part001
    + surrogateDiagTailX0RatChunk001Sub001Block021Part002
    + surrogateDiagTailX0RatChunk001Sub001Block021Part003
    + surrogateDiagTailX0RatChunk001Sub001Block021Part004
    + surrogateDiagTailX0RatChunk001Sub001Block021Part005
    + surrogateDiagTailX0RatChunk001Sub001Block021Part006
    + surrogateDiagTailX0RatChunk001Sub001Block021Part007
    + surrogateDiagTailX0RatChunk001Sub001Block021Part008
    + surrogateDiagTailX0RatChunk001Sub001Block021Part009

def surrogateDiagonalTailChunk001Sub001Block021MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block021Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block021Part010
    + surrogateDiagTailX0RatChunk001Sub001Block021Part011
    + surrogateDiagTailX0RatChunk001Sub001Block021Part012
    + surrogateDiagTailX0RatChunk001Sub001Block021Part013
    + surrogateDiagTailX0RatChunk001Sub001Block021Part014
    + surrogateDiagTailX0RatChunk001Sub001Block021Part015
    + surrogateDiagTailX0RatChunk001Sub001Block021Part016
    + surrogateDiagTailX0RatChunk001Sub001Block021Part017
    + surrogateDiagTailX0RatChunk001Sub001Block021Part018
    + surrogateDiagTailX0RatChunk001Sub001Block021Part019

def surrogateDiagonalTailChunk001Sub001Block021TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block021Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block021Part020
    + surrogateDiagTailX0RatChunk001Sub001Block021Part021
    + surrogateDiagTailX0RatChunk001Sub001Block021Part022
    + surrogateDiagTailX0RatChunk001Sub001Block021Part023
    + surrogateDiagTailX0RatChunk001Sub001Block021Part024

def surrogateDiagonalTailChunk001Sub001Block021Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block021HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block021MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block021TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block021 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block021Part000
    + surrogateDiagTailX0RatChunk001Sub001Block021Part001
    + surrogateDiagTailX0RatChunk001Sub001Block021Part002
    + surrogateDiagTailX0RatChunk001Sub001Block021Part003
    + surrogateDiagTailX0RatChunk001Sub001Block021Part004
    + surrogateDiagTailX0RatChunk001Sub001Block021Part005
    + surrogateDiagTailX0RatChunk001Sub001Block021Part006
    + surrogateDiagTailX0RatChunk001Sub001Block021Part007
    + surrogateDiagTailX0RatChunk001Sub001Block021Part008
    + surrogateDiagTailX0RatChunk001Sub001Block021Part009
    + surrogateDiagTailX0RatChunk001Sub001Block021Part010
    + surrogateDiagTailX0RatChunk001Sub001Block021Part011
    + surrogateDiagTailX0RatChunk001Sub001Block021Part012
    + surrogateDiagTailX0RatChunk001Sub001Block021Part013
    + surrogateDiagTailX0RatChunk001Sub001Block021Part014
    + surrogateDiagTailX0RatChunk001Sub001Block021Part015
    + surrogateDiagTailX0RatChunk001Sub001Block021Part016
    + surrogateDiagTailX0RatChunk001Sub001Block021Part017
    + surrogateDiagTailX0RatChunk001Sub001Block021Part018
    + surrogateDiagTailX0RatChunk001Sub001Block021Part019
    + surrogateDiagTailX0RatChunk001Sub001Block021Part020
    + surrogateDiagTailX0RatChunk001Sub001Block021Part021
    + surrogateDiagTailX0RatChunk001Sub001Block021Part022
    + surrogateDiagTailX0RatChunk001Sub001Block021Part023
    + surrogateDiagTailX0RatChunk001Sub001Block021Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block021_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block021Head + surrogateDiagTailX0RatChunk001Sub001Block021Mid + surrogateDiagTailX0RatChunk001Sub001Block021Tail =
      surrogateDiagTailX0RatChunk001Sub001Block021 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block021Head surrogateDiagTailX0RatChunk001Sub001Block021Mid surrogateDiagTailX0RatChunk001Sub001Block021Tail surrogateDiagTailX0RatChunk001Sub001Block021
  ring

def SurrogateDiagonalTailChunk001Sub001Block021HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block021HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block021Head

def SurrogateDiagonalTailChunk001Sub001Block021MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block021MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block021Mid

def SurrogateDiagonalTailChunk001Sub001Block021TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block021TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block021Tail

theorem surrogateDiagonalTailChunk001Sub001Block021_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block021HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block021MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block021TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block021Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block021 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block021HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block021MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block021TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block021Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block021_eq_head_add_mid_add_tail

/-- Block 022 covers tail-support indices [15550,15575) and q from 25634 to 25670. -/

def TailChunk001Sub001Block022Part000SupportExplicit : Finset ℕ :=
  ([25634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part000 : ℚ :=
  (8408071127 : ℚ) / 726885850508481600

def SurrogateDiagonalTailChunk001Sub001Block022Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25634
    = surrogateDiagTailX0RatChunk001Sub001Block022Part000

theorem surrogateDiagonalTailChunk001Sub001Block022Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part000] using hcert

def TailChunk001Sub001Block022Part001SupportExplicit : Finset ℕ :=
  ([25635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part001 : ℚ :=
  (638543919375 : ℚ) / 14527370805837037568

def SurrogateDiagonalTailChunk001Sub001Block022Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25635
    = surrogateDiagTailX0RatChunk001Sub001Block022Part001

theorem surrogateDiagonalTailChunk001Sub001Block022Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part001] using hcert

def TailChunk001Sub001Block022Part002SupportExplicit : Finset ℕ :=
  ([25637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part002 : ℚ :=
  (10598335543 : ℚ) / 37713084863006851200

def SurrogateDiagonalTailChunk001Sub001Block022Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25637
    = surrogateDiagTailX0RatChunk001Sub001Block022Part002

theorem surrogateDiagonalTailChunk001Sub001Block022Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part002] using hcert

def TailChunk001Sub001Block022Part003SupportExplicit : Finset ℕ :=
  ([25638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part003 : ℚ :=
  (285312270175 : ℚ) / 3331285283834560512

def SurrogateDiagonalTailChunk001Sub001Block022Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25638
    = surrogateDiagTailX0RatChunk001Sub001Block022Part003

theorem surrogateDiagonalTailChunk001Sub001Block022Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part003] using hcert

def TailChunk001Sub001Block022Part004SupportExplicit : Finset ℕ :=
  ([25639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block022Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25639
    = surrogateDiagTailX0RatChunk001Sub001Block022Part004

theorem surrogateDiagonalTailChunk001Sub001Block022Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part004] using hcert

def TailChunk001Sub001Block022Part005SupportExplicit : Finset ℕ :=
  ([25642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part005 : ℚ :=
  (4109451025 : ℚ) / 27017113728037152

def SurrogateDiagonalTailChunk001Sub001Block022Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25642
    = surrogateDiagTailX0RatChunk001Sub001Block022Part005

theorem surrogateDiagonalTailChunk001Sub001Block022Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part005] using hcert

def TailChunk001Sub001Block022Part006SupportExplicit : Finset ℕ :=
  ([25643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block022Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25643
    = surrogateDiagTailX0RatChunk001Sub001Block022Part006

theorem surrogateDiagonalTailChunk001Sub001Block022Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part006] using hcert

def TailChunk001Sub001Block022Part007SupportExplicit : Finset ℕ :=
  ([25645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part007 : ℚ :=
  (1768103187475 : ℚ) / 364224742794601463808

def SurrogateDiagonalTailChunk001Sub001Block022Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25645
    = surrogateDiagTailX0RatChunk001Sub001Block022Part007

theorem surrogateDiagonalTailChunk001Sub001Block022Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part007] using hcert

def TailChunk001Sub001Block022Part008SupportExplicit : Finset ℕ :=
  ([25646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part008 : ℚ :=
  (2569208265625 : ℚ) / 16896235641896506482

def SurrogateDiagonalTailChunk001Sub001Block022Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25646
    = surrogateDiagTailX0RatChunk001Sub001Block022Part008

theorem surrogateDiagonalTailChunk001Sub001Block022Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part008] using hcert

def TailChunk001Sub001Block022Part009SupportExplicit : Finset ℕ :=
  ([25647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part009 : ℚ :=
  (4484659555225 : ℚ) / 195795604594581424128

def SurrogateDiagonalTailChunk001Sub001Block022Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25647
    = surrogateDiagTailX0RatChunk001Sub001Block022Part009

theorem surrogateDiagonalTailChunk001Sub001Block022Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part009] using hcert

def TailChunk001Sub001Block022Part010SupportExplicit : Finset ℕ :=
  ([25649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part010 : ℚ :=
  (489754314025 : ℚ) / 784114500912201105408

def SurrogateDiagonalTailChunk001Sub001Block022Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25649
    = surrogateDiagTailX0RatChunk001Sub001Block022Part010

theorem surrogateDiagonalTailChunk001Sub001Block022Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part010] using hcert

def TailChunk001Sub001Block022Part011SupportExplicit : Finset ℕ :=
  ([25651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part011 : ℚ :=
  (15073816075 : ℚ) / 146633994723562881024

def SurrogateDiagonalTailChunk001Sub001Block022Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25651
    = surrogateDiagTailX0RatChunk001Sub001Block022Part011

theorem surrogateDiagonalTailChunk001Sub001Block022Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part011] using hcert

def TailChunk001Sub001Block022Part012SupportExplicit : Finset ℕ :=
  ([25653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part012 : ℚ :=
  (538718190875 : ℚ) / 20813813258388504576

def SurrogateDiagonalTailChunk001Sub001Block022Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25653
    = surrogateDiagTailX0RatChunk001Sub001Block022Part012

theorem surrogateDiagonalTailChunk001Sub001Block022Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part012] using hcert

def TailChunk001Sub001Block022Part013SupportExplicit : Finset ℕ :=
  ([25654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part013 : ℚ :=
  (12490463009 : ℚ) / 78780557961000000

def SurrogateDiagonalTailChunk001Sub001Block022Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25654
    = surrogateDiagTailX0RatChunk001Sub001Block022Part013

theorem surrogateDiagonalTailChunk001Sub001Block022Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part013] using hcert

def TailChunk001Sub001Block022Part014SupportExplicit : Finset ℕ :=
  ([25655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part014 : ℚ :=
  (19614791975 : ℚ) / 2481103703068950528

def SurrogateDiagonalTailChunk001Sub001Block022Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25655
    = surrogateDiagTailX0RatChunk001Sub001Block022Part014

theorem surrogateDiagonalTailChunk001Sub001Block022Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part014] using hcert

def TailChunk001Sub001Block022Part015SupportExplicit : Finset ℕ :=
  ([25657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block022Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25657
    = surrogateDiagTailX0RatChunk001Sub001Block022Part015

theorem surrogateDiagonalTailChunk001Sub001Block022Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part015] using hcert

def TailChunk001Sub001Block022Part016SupportExplicit : Finset ℕ :=
  ([25658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part016 : ℚ :=
  (2571613140625 : ℚ) / 16927883932254649632

def SurrogateDiagonalTailChunk001Sub001Block022Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25658
    = surrogateDiagTailX0RatChunk001Sub001Block022Part016

theorem surrogateDiagonalTailChunk001Sub001Block022Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part016] using hcert

def TailChunk001Sub001Block022Part017SupportExplicit : Finset ℕ :=
  ([25661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part017 : ℚ :=
  (8687752825 : ℚ) / 63144578708082763848

def SurrogateDiagonalTailChunk001Sub001Block022Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25661
    = surrogateDiagTailX0RatChunk001Sub001Block022Part017

theorem surrogateDiagonalTailChunk001Sub001Block022Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part017] using hcert

def TailChunk001Sub001Block022Part018SupportExplicit : Finset ℕ :=
  ([25662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part018 : ℚ :=
  (1920672057125 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk001Sub001Block022Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25662
    = surrogateDiagTailX0RatChunk001Sub001Block022Part018

theorem surrogateDiagonalTailChunk001Sub001Block022Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part018] using hcert

def TailChunk001Sub001Block022Part019SupportExplicit : Finset ℕ :=
  ([25663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part019 : ℚ :=
  (6827697199 : ℚ) / 7395048782557708800

def SurrogateDiagonalTailChunk001Sub001Block022Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25663
    = surrogateDiagTailX0RatChunk001Sub001Block022Part019

theorem surrogateDiagonalTailChunk001Sub001Block022Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part019] using hcert

def TailChunk001Sub001Block022Part020SupportExplicit : Finset ℕ :=
  ([25665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part020 : ℚ :=
  (3670885742875 : ℚ) / 71241147553884930048

def SurrogateDiagonalTailChunk001Sub001Block022Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25665
    = surrogateDiagTailX0RatChunk001Sub001Block022Part020

theorem surrogateDiagonalTailChunk001Sub001Block022Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part020] using hcert

def TailChunk001Sub001Block022Part021SupportExplicit : Finset ℕ :=
  ([25666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part021 : ℚ :=
  (512461793 : ℚ) / 3159249835622400

def SurrogateDiagonalTailChunk001Sub001Block022Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25666
    = surrogateDiagTailX0RatChunk001Sub001Block022Part021

theorem surrogateDiagonalTailChunk001Sub001Block022Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part021] using hcert

def TailChunk001Sub001Block022Part022SupportExplicit : Finset ℕ :=
  ([25667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block022Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25667
    = surrogateDiagTailX0RatChunk001Sub001Block022Part022

theorem surrogateDiagonalTailChunk001Sub001Block022Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part022] using hcert

def TailChunk001Sub001Block022Part023SupportExplicit : Finset ℕ :=
  ([25669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part023 : ℚ :=
  (1079443654825 : ℚ) / 462303089367038558208

def SurrogateDiagonalTailChunk001Sub001Block022Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25669
    = surrogateDiagTailX0RatChunk001Sub001Block022Part023

theorem surrogateDiagonalTailChunk001Sub001Block022Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part023] using hcert

def TailChunk001Sub001Block022Part024SupportExplicit : Finset ℕ :=
  ([25670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block022Part024 : ℚ :=
  (251570180161 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub001Block022Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25670
    = surrogateDiagTailX0RatChunk001Sub001Block022Part024

theorem surrogateDiagonalTailChunk001Sub001Block022Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block022Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block022Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block022Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block022Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block022Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block022HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block022Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block022Part000
    + surrogateDiagTailX0RatChunk001Sub001Block022Part001
    + surrogateDiagTailX0RatChunk001Sub001Block022Part002
    + surrogateDiagTailX0RatChunk001Sub001Block022Part003
    + surrogateDiagTailX0RatChunk001Sub001Block022Part004
    + surrogateDiagTailX0RatChunk001Sub001Block022Part005
    + surrogateDiagTailX0RatChunk001Sub001Block022Part006
    + surrogateDiagTailX0RatChunk001Sub001Block022Part007
    + surrogateDiagTailX0RatChunk001Sub001Block022Part008
    + surrogateDiagTailX0RatChunk001Sub001Block022Part009

def surrogateDiagonalTailChunk001Sub001Block022MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block022Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block022Part010
    + surrogateDiagTailX0RatChunk001Sub001Block022Part011
    + surrogateDiagTailX0RatChunk001Sub001Block022Part012
    + surrogateDiagTailX0RatChunk001Sub001Block022Part013
    + surrogateDiagTailX0RatChunk001Sub001Block022Part014
    + surrogateDiagTailX0RatChunk001Sub001Block022Part015
    + surrogateDiagTailX0RatChunk001Sub001Block022Part016
    + surrogateDiagTailX0RatChunk001Sub001Block022Part017
    + surrogateDiagTailX0RatChunk001Sub001Block022Part018
    + surrogateDiagTailX0RatChunk001Sub001Block022Part019

def surrogateDiagonalTailChunk001Sub001Block022TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block022Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block022Part020
    + surrogateDiagTailX0RatChunk001Sub001Block022Part021
    + surrogateDiagTailX0RatChunk001Sub001Block022Part022
    + surrogateDiagTailX0RatChunk001Sub001Block022Part023
    + surrogateDiagTailX0RatChunk001Sub001Block022Part024

def surrogateDiagonalTailChunk001Sub001Block022Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block022HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block022MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block022TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block022 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block022Part000
    + surrogateDiagTailX0RatChunk001Sub001Block022Part001
    + surrogateDiagTailX0RatChunk001Sub001Block022Part002
    + surrogateDiagTailX0RatChunk001Sub001Block022Part003
    + surrogateDiagTailX0RatChunk001Sub001Block022Part004
    + surrogateDiagTailX0RatChunk001Sub001Block022Part005
    + surrogateDiagTailX0RatChunk001Sub001Block022Part006
    + surrogateDiagTailX0RatChunk001Sub001Block022Part007
    + surrogateDiagTailX0RatChunk001Sub001Block022Part008
    + surrogateDiagTailX0RatChunk001Sub001Block022Part009
    + surrogateDiagTailX0RatChunk001Sub001Block022Part010
    + surrogateDiagTailX0RatChunk001Sub001Block022Part011
    + surrogateDiagTailX0RatChunk001Sub001Block022Part012
    + surrogateDiagTailX0RatChunk001Sub001Block022Part013
    + surrogateDiagTailX0RatChunk001Sub001Block022Part014
    + surrogateDiagTailX0RatChunk001Sub001Block022Part015
    + surrogateDiagTailX0RatChunk001Sub001Block022Part016
    + surrogateDiagTailX0RatChunk001Sub001Block022Part017
    + surrogateDiagTailX0RatChunk001Sub001Block022Part018
    + surrogateDiagTailX0RatChunk001Sub001Block022Part019
    + surrogateDiagTailX0RatChunk001Sub001Block022Part020
    + surrogateDiagTailX0RatChunk001Sub001Block022Part021
    + surrogateDiagTailX0RatChunk001Sub001Block022Part022
    + surrogateDiagTailX0RatChunk001Sub001Block022Part023
    + surrogateDiagTailX0RatChunk001Sub001Block022Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block022_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block022Head + surrogateDiagTailX0RatChunk001Sub001Block022Mid + surrogateDiagTailX0RatChunk001Sub001Block022Tail =
      surrogateDiagTailX0RatChunk001Sub001Block022 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block022Head surrogateDiagTailX0RatChunk001Sub001Block022Mid surrogateDiagTailX0RatChunk001Sub001Block022Tail surrogateDiagTailX0RatChunk001Sub001Block022
  ring

def SurrogateDiagonalTailChunk001Sub001Block022HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block022HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block022Head

def SurrogateDiagonalTailChunk001Sub001Block022MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block022MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block022Mid

def SurrogateDiagonalTailChunk001Sub001Block022TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block022TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block022Tail

theorem surrogateDiagonalTailChunk001Sub001Block022_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block022HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block022MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block022TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block022Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block022 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block022HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block022MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block022TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block022Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block022_eq_head_add_mid_add_tail

/-- Block 023 covers tail-support indices [15575,15600) and q from 25671 to 25709. -/

def TailChunk001Sub001Block023Part000SupportExplicit : Finset ℕ :=
  ([25671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part000 : ℚ :=
  (17722891975 : ℚ) / 759283956440722944

def SurrogateDiagonalTailChunk001Sub001Block023Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25671
    = surrogateDiagTailX0RatChunk001Sub001Block023Part000

theorem surrogateDiagonalTailChunk001Sub001Block023Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part000] using hcert

def TailChunk001Sub001Block023Part001SupportExplicit : Finset ℕ :=
  ([25673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block023Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25673
    = surrogateDiagTailX0RatChunk001Sub001Block023Part001

theorem surrogateDiagonalTailChunk001Sub001Block023Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part001] using hcert

def TailChunk001Sub001Block023Part002SupportExplicit : Finset ℕ :=
  ([25674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part002 : ℚ :=
  (195984724951 : ℚ) / 362688458162995200

def SurrogateDiagonalTailChunk001Sub001Block023Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25674
    = surrogateDiagTailX0RatChunk001Sub001Block023Part002

theorem surrogateDiagonalTailChunk001Sub001Block023Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part002] using hcert

def TailChunk001Sub001Block023Part003SupportExplicit : Finset ℕ :=
  ([25678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part003 : ℚ :=
  (4907068855475 : ℚ) / 30096172086496257024

def SurrogateDiagonalTailChunk001Sub001Block023Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25678
    = surrogateDiagTailX0RatChunk001Sub001Block023Part003

theorem surrogateDiagonalTailChunk001Sub001Block023Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part003] using hcert

def TailChunk001Sub001Block023Part004SupportExplicit : Finset ℕ :=
  ([25679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block023Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25679
    = surrogateDiagTailX0RatChunk001Sub001Block023Part004

theorem surrogateDiagonalTailChunk001Sub001Block023Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part004] using hcert

def TailChunk001Sub001Block023Part005SupportExplicit : Finset ℕ :=
  ([25681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part005 : ℚ :=
  (6030709549 : ℚ) / 40335645676032000000

def SurrogateDiagonalTailChunk001Sub001Block023Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25681
    = surrogateDiagTailX0RatChunk001Sub001Block023Part005

theorem surrogateDiagonalTailChunk001Sub001Block023Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part005] using hcert

def TailChunk001Sub001Block023Part006SupportExplicit : Finset ℕ :=
  ([25682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part006 : ℚ :=
  (4122282025 : ℚ) / 27186102196572672

def SurrogateDiagonalTailChunk001Sub001Block023Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25682
    = surrogateDiagTailX0RatChunk001Sub001Block023Part006

theorem surrogateDiagonalTailChunk001Sub001Block023Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part006] using hcert

def TailChunk001Sub001Block023Part007SupportExplicit : Finset ℕ :=
  ([25683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part007 : ℚ :=
  (657172902925 : ℚ) / 115620985478548113408

def SurrogateDiagonalTailChunk001Sub001Block023Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25683
    = surrogateDiagTailX0RatChunk001Sub001Block023Part007

theorem surrogateDiagonalTailChunk001Sub001Block023Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part007] using hcert

def TailChunk001Sub001Block023Part008SupportExplicit : Finset ℕ :=
  ([25685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part008 : ℚ :=
  (7650915517 : ℚ) / 1207453687850680320

def SurrogateDiagonalTailChunk001Sub001Block023Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25685
    = surrogateDiagTailX0RatChunk001Sub001Block023Part008

theorem surrogateDiagonalTailChunk001Sub001Block023Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part008] using hcert

def TailChunk001Sub001Block023Part009SupportExplicit : Finset ℕ :=
  ([25687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part009 : ℚ :=
  (22987270843 : ℚ) / 34078036991685427200

def SurrogateDiagonalTailChunk001Sub001Block023Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25687
    = surrogateDiagTailX0RatChunk001Sub001Block023Part009

theorem surrogateDiagonalTailChunk001Sub001Block023Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part009] using hcert

def TailChunk001Sub001Block023Part010SupportExplicit : Finset ℕ :=
  ([25689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part010 : ℚ :=
  (41675 : ℚ) / 14330773311808896

def SurrogateDiagonalTailChunk001Sub001Block023Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25689
    = surrogateDiagTailX0RatChunk001Sub001Block023Part010

theorem surrogateDiagonalTailChunk001Sub001Block023Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part010] using hcert

def TailChunk001Sub001Block023Part011SupportExplicit : Finset ℕ :=
  ([25690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part011 : ℚ :=
  (5483339376025 : ℚ) / 14886622218413703168

def SurrogateDiagonalTailChunk001Sub001Block023Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25690
    = surrogateDiagTailX0RatChunk001Sub001Block023Part011

theorem surrogateDiagonalTailChunk001Sub001Block023Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part011] using hcert

def TailChunk001Sub001Block023Part012SupportExplicit : Finset ℕ :=
  ([25691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part012 : ℚ :=
  (395758643275 : ℚ) / 908603406201610487808

def SurrogateDiagonalTailChunk001Sub001Block023Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25691
    = surrogateDiagTailX0RatChunk001Sub001Block023Part012

theorem surrogateDiagonalTailChunk001Sub001Block023Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part012] using hcert

def TailChunk001Sub001Block023Part013SupportExplicit : Finset ℕ :=
  ([25693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block023Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25693
    = surrogateDiagTailX0RatChunk001Sub001Block023Part013

theorem surrogateDiagonalTailChunk001Sub001Block023Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part013] using hcert

def TailChunk001Sub001Block023Part014SupportExplicit : Finset ℕ :=
  ([25694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part014 : ℚ :=
  (9704762009125 : ℚ) / 58660810829256050688

def SurrogateDiagonalTailChunk001Sub001Block023Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25694
    = surrogateDiagTailX0RatChunk001Sub001Block023Part014

theorem surrogateDiagonalTailChunk001Sub001Block023Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part014] using hcert

def TailChunk001Sub001Block023Part015SupportExplicit : Finset ℕ :=
  ([25697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part015 : ℚ :=
  (33747247333 : ℚ) / 23515602410462083200

def SurrogateDiagonalTailChunk001Sub001Block023Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25697
    = surrogateDiagTailX0RatChunk001Sub001Block023Part015

theorem surrogateDiagonalTailChunk001Sub001Block023Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part015] using hcert

def TailChunk001Sub001Block023Part016SupportExplicit : Finset ℕ :=
  ([25698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part016 : ℚ :=
  (4584505571725 : ℚ) / 13450347145705876608

def SurrogateDiagonalTailChunk001Sub001Block023Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25698
    = surrogateDiagTailX0RatChunk001Sub001Block023Part016

theorem surrogateDiagonalTailChunk001Sub001Block023Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part016] using hcert

def TailChunk001Sub001Block023Part017SupportExplicit : Finset ℕ :=
  ([25699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part017 : ℚ :=
  (10647905971 : ℚ) / 38079673517357107200

def SurrogateDiagonalTailChunk001Sub001Block023Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25699
    = surrogateDiagTailX0RatChunk001Sub001Block023Part017

theorem surrogateDiagonalTailChunk001Sub001Block023Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part017] using hcert

def TailChunk001Sub001Block023Part018SupportExplicit : Finset ℕ :=
  ([25701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part018 : ℚ :=
  (58451192225 : ℚ) / 19439514452154617856

def SurrogateDiagonalTailChunk001Sub001Block023Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25701
    = surrogateDiagTailX0RatChunk001Sub001Block023Part018

theorem surrogateDiagonalTailChunk001Sub001Block023Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part018] using hcert

def TailChunk001Sub001Block023Part019SupportExplicit : Finset ℕ :=
  ([25702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part019 : ℚ :=
  (99998492401 : ℚ) / 630244463688000000

def SurrogateDiagonalTailChunk001Sub001Block023Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25702
    = surrogateDiagTailX0RatChunk001Sub001Block023Part019

theorem surrogateDiagonalTailChunk001Sub001Block023Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part019] using hcert

def TailChunk001Sub001Block023Part020SupportExplicit : Finset ℕ :=
  ([25703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block023Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25703
    = surrogateDiagTailX0RatChunk001Sub001Block023Part020

theorem surrogateDiagonalTailChunk001Sub001Block023Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part020] using hcert

def TailChunk001Sub001Block023Part021SupportExplicit : Finset ℕ :=
  ([25705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part021 : ℚ :=
  (873582948575 : ℚ) / 198762813338255622144

def SurrogateDiagonalTailChunk001Sub001Block023Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25705
    = surrogateDiagTailX0RatChunk001Sub001Block023Part021

theorem surrogateDiagonalTailChunk001Sub001Block023Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part021] using hcert

def TailChunk001Sub001Block023Part022SupportExplicit : Finset ℕ :=
  ([25706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part022 : ℚ :=
  (2581243890625 : ℚ) / 17054921903946085152

def SurrogateDiagonalTailChunk001Sub001Block023Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25706
    = surrogateDiagTailX0RatChunk001Sub001Block023Part022

theorem surrogateDiagonalTailChunk001Sub001Block023Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part022] using hcert

def TailChunk001Sub001Block023Part023SupportExplicit : Finset ℕ :=
  ([25707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part023 : ℚ :=
  (234979847 : ℚ) / 28671179489280000

def SurrogateDiagonalTailChunk001Sub001Block023Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25707
    = surrogateDiagTailX0RatChunk001Sub001Block023Part023

theorem surrogateDiagonalTailChunk001Sub001Block023Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part023] using hcert

def TailChunk001Sub001Block023Part024SupportExplicit : Finset ℕ :=
  ([25709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block023Part024 : ℚ :=
  (181749912625 : ℚ) / 995013003484795171968

def SurrogateDiagonalTailChunk001Sub001Block023Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25709
    = surrogateDiagTailX0RatChunk001Sub001Block023Part024

theorem surrogateDiagonalTailChunk001Sub001Block023Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block023Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block023Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block023Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block023Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block023Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block023HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block023Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block023Part000
    + surrogateDiagTailX0RatChunk001Sub001Block023Part001
    + surrogateDiagTailX0RatChunk001Sub001Block023Part002
    + surrogateDiagTailX0RatChunk001Sub001Block023Part003
    + surrogateDiagTailX0RatChunk001Sub001Block023Part004
    + surrogateDiagTailX0RatChunk001Sub001Block023Part005
    + surrogateDiagTailX0RatChunk001Sub001Block023Part006
    + surrogateDiagTailX0RatChunk001Sub001Block023Part007
    + surrogateDiagTailX0RatChunk001Sub001Block023Part008
    + surrogateDiagTailX0RatChunk001Sub001Block023Part009

def surrogateDiagonalTailChunk001Sub001Block023MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block023Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block023Part010
    + surrogateDiagTailX0RatChunk001Sub001Block023Part011
    + surrogateDiagTailX0RatChunk001Sub001Block023Part012
    + surrogateDiagTailX0RatChunk001Sub001Block023Part013
    + surrogateDiagTailX0RatChunk001Sub001Block023Part014
    + surrogateDiagTailX0RatChunk001Sub001Block023Part015
    + surrogateDiagTailX0RatChunk001Sub001Block023Part016
    + surrogateDiagTailX0RatChunk001Sub001Block023Part017
    + surrogateDiagTailX0RatChunk001Sub001Block023Part018
    + surrogateDiagTailX0RatChunk001Sub001Block023Part019

def surrogateDiagonalTailChunk001Sub001Block023TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block023Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block023Part020
    + surrogateDiagTailX0RatChunk001Sub001Block023Part021
    + surrogateDiagTailX0RatChunk001Sub001Block023Part022
    + surrogateDiagTailX0RatChunk001Sub001Block023Part023
    + surrogateDiagTailX0RatChunk001Sub001Block023Part024

def surrogateDiagonalTailChunk001Sub001Block023Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block023HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block023MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block023TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block023 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block023Part000
    + surrogateDiagTailX0RatChunk001Sub001Block023Part001
    + surrogateDiagTailX0RatChunk001Sub001Block023Part002
    + surrogateDiagTailX0RatChunk001Sub001Block023Part003
    + surrogateDiagTailX0RatChunk001Sub001Block023Part004
    + surrogateDiagTailX0RatChunk001Sub001Block023Part005
    + surrogateDiagTailX0RatChunk001Sub001Block023Part006
    + surrogateDiagTailX0RatChunk001Sub001Block023Part007
    + surrogateDiagTailX0RatChunk001Sub001Block023Part008
    + surrogateDiagTailX0RatChunk001Sub001Block023Part009
    + surrogateDiagTailX0RatChunk001Sub001Block023Part010
    + surrogateDiagTailX0RatChunk001Sub001Block023Part011
    + surrogateDiagTailX0RatChunk001Sub001Block023Part012
    + surrogateDiagTailX0RatChunk001Sub001Block023Part013
    + surrogateDiagTailX0RatChunk001Sub001Block023Part014
    + surrogateDiagTailX0RatChunk001Sub001Block023Part015
    + surrogateDiagTailX0RatChunk001Sub001Block023Part016
    + surrogateDiagTailX0RatChunk001Sub001Block023Part017
    + surrogateDiagTailX0RatChunk001Sub001Block023Part018
    + surrogateDiagTailX0RatChunk001Sub001Block023Part019
    + surrogateDiagTailX0RatChunk001Sub001Block023Part020
    + surrogateDiagTailX0RatChunk001Sub001Block023Part021
    + surrogateDiagTailX0RatChunk001Sub001Block023Part022
    + surrogateDiagTailX0RatChunk001Sub001Block023Part023
    + surrogateDiagTailX0RatChunk001Sub001Block023Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block023_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block023Head + surrogateDiagTailX0RatChunk001Sub001Block023Mid + surrogateDiagTailX0RatChunk001Sub001Block023Tail =
      surrogateDiagTailX0RatChunk001Sub001Block023 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block023Head surrogateDiagTailX0RatChunk001Sub001Block023Mid surrogateDiagTailX0RatChunk001Sub001Block023Tail surrogateDiagTailX0RatChunk001Sub001Block023
  ring

def SurrogateDiagonalTailChunk001Sub001Block023HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block023HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block023Head

def SurrogateDiagonalTailChunk001Sub001Block023MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block023MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block023Mid

def SurrogateDiagonalTailChunk001Sub001Block023TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block023TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block023Tail

theorem surrogateDiagonalTailChunk001Sub001Block023_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block023HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block023MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block023TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block023Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block023 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block023HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block023MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block023TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block023Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block023_eq_head_add_mid_add_tail

/-- Block 024 covers tail-support indices [15600,15625) and q from 25710 to 25751. -/

def TailChunk001Sub001Block024Part000SupportExplicit : Finset ℕ :=
  ([25710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part000 : ℚ :=
  (1099849127175 : ℚ) / 1832992174438875136

def SurrogateDiagonalTailChunk001Sub001Block024Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25710
    = surrogateDiagTailX0RatChunk001Sub001Block024Part000

theorem surrogateDiagonalTailChunk001Sub001Block024Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part000] using hcert

def TailChunk001Sub001Block024Part001SupportExplicit : Finset ℕ :=
  ([25711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part001 : ℚ :=
  (844598933425 : ℚ) / 589172612411871756288

def SurrogateDiagonalTailChunk001Sub001Block024Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25711
    = surrogateDiagTailX0RatChunk001Sub001Block024Part001

theorem surrogateDiagonalTailChunk001Sub001Block024Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part001] using hcert

def TailChunk001Sub001Block024Part002SupportExplicit : Finset ℕ :=
  ([25714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part002 : ℚ :=
  (8111517042325 : ℚ) / 37795468053938208768

def SurrogateDiagonalTailChunk001Sub001Block024Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25714
    = surrogateDiagTailX0RatChunk001Sub001Block024Part002

theorem surrogateDiagonalTailChunk001Sub001Block024Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part002] using hcert

def TailChunk001Sub001Block024Part003SupportExplicit : Finset ℕ :=
  ([25715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part003 : ℚ :=
  (438526203325 : ℚ) / 97483964204434194432

def SurrogateDiagonalTailChunk001Sub001Block024Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25715
    = surrogateDiagTailX0RatChunk001Sub001Block024Part003

theorem surrogateDiagonalTailChunk001Sub001Block024Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part003] using hcert

def TailChunk001Sub001Block024Part004SupportExplicit : Finset ℕ :=
  ([25717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block024Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25717
    = surrogateDiagTailX0RatChunk001Sub001Block024Part004

theorem surrogateDiagonalTailChunk001Sub001Block024Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part004] using hcert

def TailChunk001Sub001Block024Part005SupportExplicit : Finset ℕ :=
  ([25718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part005 : ℚ :=
  (26473679611 : ℚ) / 98429256340485120

def SurrogateDiagonalTailChunk001Sub001Block024Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25718
    = surrogateDiagTailX0RatChunk001Sub001Block024Part005

theorem surrogateDiagonalTailChunk001Sub001Block024Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part005] using hcert

def TailChunk001Sub001Block024Part006SupportExplicit : Finset ℕ :=
  ([25719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part006 : ℚ :=
  (125025 : ℚ) / 43193523850446848

def SurrogateDiagonalTailChunk001Sub001Block024Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25719
    = surrogateDiagTailX0RatChunk001Sub001Block024Part006

theorem surrogateDiagonalTailChunk001Sub001Block024Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part006] using hcert

def TailChunk001Sub001Block024Part007SupportExplicit : Finset ℕ :=
  ([25723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part007 : ℚ :=
  (302811239575 : ℚ) / 947095715192171317248

def SurrogateDiagonalTailChunk001Sub001Block024Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25723
    = surrogateDiagTailX0RatChunk001Sub001Block024Part007

theorem surrogateDiagonalTailChunk001Sub001Block024Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part007] using hcert

def TailChunk001Sub001Block024Part008SupportExplicit : Finset ℕ :=
  ([25726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part008 : ℚ :=
  (4715895795725 : ℚ) / 27407767871145452544

def SurrogateDiagonalTailChunk001Sub001Block024Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25726
    = surrogateDiagTailX0RatChunk001Sub001Block024Part008

theorem surrogateDiagonalTailChunk001Sub001Block024Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part008] using hcert

def TailChunk001Sub001Block024Part009SupportExplicit : Finset ℕ :=
  ([25727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part009 : ℚ :=
  (92131292225 : ℚ) / 99212639765900011776

def SurrogateDiagonalTailChunk001Sub001Block024Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25727
    = surrogateDiagTailX0RatChunk001Sub001Block024Part009

theorem surrogateDiagonalTailChunk001Sub001Block024Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part009] using hcert

def TailChunk001Sub001Block024Part010SupportExplicit : Finset ℕ :=
  ([25729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part010 : ℚ :=
  (857839397 : ℚ) / 933931232257172100

def SurrogateDiagonalTailChunk001Sub001Block024Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25729
    = surrogateDiagTailX0RatChunk001Sub001Block024Part010

theorem surrogateDiagonalTailChunk001Sub001Block024Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part010] using hcert

def TailChunk001Sub001Block024Part011SupportExplicit : Finset ℕ :=
  ([25730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part011 : ℚ :=
  (10935451481 : ℚ) / 39071132728012800

def SurrogateDiagonalTailChunk001Sub001Block024Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25730
    = surrogateDiagTailX0RatChunk001Sub001Block024Part011

theorem surrogateDiagonalTailChunk001Sub001Block024Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part011] using hcert

def TailChunk001Sub001Block024Part012SupportExplicit : Finset ℕ :=
  ([25733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block024Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25733
    = surrogateDiagTailX0RatChunk001Sub001Block024Part012

theorem surrogateDiagonalTailChunk001Sub001Block024Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part012] using hcert

def TailChunk001Sub001Block024Part013SupportExplicit : Finset ℕ :=
  ([25734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part013 : ℚ :=
  (4597360571125 : ℚ) / 13525893024042713088

def SurrogateDiagonalTailChunk001Sub001Block024Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25734
    = surrogateDiagTailX0RatChunk001Sub001Block024Part013

theorem surrogateDiagonalTailChunk001Sub001Block024Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part013] using hcert

def TailChunk001Sub001Block024Part014SupportExplicit : Finset ℕ :=
  ([25735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part014 : ℚ :=
  (552110931375 : ℚ) / 149632074477071865856

def SurrogateDiagonalTailChunk001Sub001Block024Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25735
    = surrogateDiagTailX0RatChunk001Sub001Block024Part014

theorem surrogateDiagonalTailChunk001Sub001Block024Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part014] using hcert

def TailChunk001Sub001Block024Part015SupportExplicit : Finset ℕ :=
  ([25737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part015 : ℚ :=
  (1938721225 : ℚ) / 1359675879089577984

def SurrogateDiagonalTailChunk001Sub001Block024Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25737
    = surrogateDiagTailX0RatChunk001Sub001Block024Part015

theorem surrogateDiagonalTailChunk001Sub001Block024Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part015] using hcert

def TailChunk001Sub001Block024Part016SupportExplicit : Finset ℕ :=
  ([25738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part016 : ℚ :=
  (4682519855075 : ℚ) / 26764798359622385664

def SurrogateDiagonalTailChunk001Sub001Block024Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25738
    = surrogateDiagTailX0RatChunk001Sub001Block024Part016

theorem surrogateDiagonalTailChunk001Sub001Block024Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part016] using hcert

def TailChunk001Sub001Block024Part017SupportExplicit : Finset ℕ :=
  ([25739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part017 : ℚ :=
  (845329523375 : ℚ) / 295872005578655130624

def SurrogateDiagonalTailChunk001Sub001Block024Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25739
    = surrogateDiagTailX0RatChunk001Sub001Block024Part017

theorem surrogateDiagonalTailChunk001Sub001Block024Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part017] using hcert

def TailChunk001Sub001Block024Part018SupportExplicit : Finset ℕ :=
  ([25741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block024Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25741
    = surrogateDiagTailX0RatChunk001Sub001Block024Part018

theorem surrogateDiagonalTailChunk001Sub001Block024Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part018] using hcert

def TailChunk001Sub001Block024Part019SupportExplicit : Finset ℕ :=
  ([25742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part019 : ℚ :=
  (2223480881 : ℚ) / 14005432526400000

def SurrogateDiagonalTailChunk001Sub001Block024Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25742
    = surrogateDiagTailX0RatChunk001Sub001Block024Part019

theorem surrogateDiagonalTailChunk001Sub001Block024Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part019] using hcert

def TailChunk001Sub001Block024Part020SupportExplicit : Finset ℕ :=
  ([25743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part020 : ℚ :=
  (1667 : ℚ) / 578066597222400

def SurrogateDiagonalTailChunk001Sub001Block024Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25743
    = surrogateDiagTailX0RatChunk001Sub001Block024Part020

theorem surrogateDiagonalTailChunk001Sub001Block024Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part020] using hcert

def TailChunk001Sub001Block024Part021SupportExplicit : Finset ℕ :=
  ([25745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part021 : ℚ :=
  (23748302549 : ℚ) / 4761575093425766400

def SurrogateDiagonalTailChunk001Sub001Block024Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25745
    = surrogateDiagTailX0RatChunk001Sub001Block024Part021

theorem surrogateDiagonalTailChunk001Sub001Block024Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part021] using hcert

def TailChunk001Sub001Block024Part022SupportExplicit : Finset ℕ :=
  ([25746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part022 : ℚ :=
  (919723510225 : ℚ) / 1818433988925530112

def SurrogateDiagonalTailChunk001Sub001Block024Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25746
    = surrogateDiagTailX0RatChunk001Sub001Block024Part022

theorem surrogateDiagonalTailChunk001Sub001Block024Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part022] using hcert

def TailChunk001Sub001Block024Part023SupportExplicit : Finset ℕ :=
  ([25747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block024Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25747
    = surrogateDiagTailX0RatChunk001Sub001Block024Part023

theorem surrogateDiagonalTailChunk001Sub001Block024Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part023] using hcert

def TailChunk001Sub001Block024Part024SupportExplicit : Finset ℕ :=
  ([25751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block024Part024 : ℚ :=
  (2291469277 : ℚ) / 2499015983256000000

def SurrogateDiagonalTailChunk001Sub001Block024Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25751
    = surrogateDiagTailX0RatChunk001Sub001Block024Part024

theorem surrogateDiagonalTailChunk001Sub001Block024Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block024Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block024Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block024Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block024Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block024Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block024HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block024Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block024Part000
    + surrogateDiagTailX0RatChunk001Sub001Block024Part001
    + surrogateDiagTailX0RatChunk001Sub001Block024Part002
    + surrogateDiagTailX0RatChunk001Sub001Block024Part003
    + surrogateDiagTailX0RatChunk001Sub001Block024Part004
    + surrogateDiagTailX0RatChunk001Sub001Block024Part005
    + surrogateDiagTailX0RatChunk001Sub001Block024Part006
    + surrogateDiagTailX0RatChunk001Sub001Block024Part007
    + surrogateDiagTailX0RatChunk001Sub001Block024Part008
    + surrogateDiagTailX0RatChunk001Sub001Block024Part009

def surrogateDiagonalTailChunk001Sub001Block024MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block024Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block024Part010
    + surrogateDiagTailX0RatChunk001Sub001Block024Part011
    + surrogateDiagTailX0RatChunk001Sub001Block024Part012
    + surrogateDiagTailX0RatChunk001Sub001Block024Part013
    + surrogateDiagTailX0RatChunk001Sub001Block024Part014
    + surrogateDiagTailX0RatChunk001Sub001Block024Part015
    + surrogateDiagTailX0RatChunk001Sub001Block024Part016
    + surrogateDiagTailX0RatChunk001Sub001Block024Part017
    + surrogateDiagTailX0RatChunk001Sub001Block024Part018
    + surrogateDiagTailX0RatChunk001Sub001Block024Part019

def surrogateDiagonalTailChunk001Sub001Block024TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block024Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block024Part020
    + surrogateDiagTailX0RatChunk001Sub001Block024Part021
    + surrogateDiagTailX0RatChunk001Sub001Block024Part022
    + surrogateDiagTailX0RatChunk001Sub001Block024Part023
    + surrogateDiagTailX0RatChunk001Sub001Block024Part024

def surrogateDiagonalTailChunk001Sub001Block024Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block024HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block024MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block024TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block024 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block024Part000
    + surrogateDiagTailX0RatChunk001Sub001Block024Part001
    + surrogateDiagTailX0RatChunk001Sub001Block024Part002
    + surrogateDiagTailX0RatChunk001Sub001Block024Part003
    + surrogateDiagTailX0RatChunk001Sub001Block024Part004
    + surrogateDiagTailX0RatChunk001Sub001Block024Part005
    + surrogateDiagTailX0RatChunk001Sub001Block024Part006
    + surrogateDiagTailX0RatChunk001Sub001Block024Part007
    + surrogateDiagTailX0RatChunk001Sub001Block024Part008
    + surrogateDiagTailX0RatChunk001Sub001Block024Part009
    + surrogateDiagTailX0RatChunk001Sub001Block024Part010
    + surrogateDiagTailX0RatChunk001Sub001Block024Part011
    + surrogateDiagTailX0RatChunk001Sub001Block024Part012
    + surrogateDiagTailX0RatChunk001Sub001Block024Part013
    + surrogateDiagTailX0RatChunk001Sub001Block024Part014
    + surrogateDiagTailX0RatChunk001Sub001Block024Part015
    + surrogateDiagTailX0RatChunk001Sub001Block024Part016
    + surrogateDiagTailX0RatChunk001Sub001Block024Part017
    + surrogateDiagTailX0RatChunk001Sub001Block024Part018
    + surrogateDiagTailX0RatChunk001Sub001Block024Part019
    + surrogateDiagTailX0RatChunk001Sub001Block024Part020
    + surrogateDiagTailX0RatChunk001Sub001Block024Part021
    + surrogateDiagTailX0RatChunk001Sub001Block024Part022
    + surrogateDiagTailX0RatChunk001Sub001Block024Part023
    + surrogateDiagTailX0RatChunk001Sub001Block024Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block024_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block024Head + surrogateDiagTailX0RatChunk001Sub001Block024Mid + surrogateDiagTailX0RatChunk001Sub001Block024Tail =
      surrogateDiagTailX0RatChunk001Sub001Block024 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block024Head surrogateDiagTailX0RatChunk001Sub001Block024Mid surrogateDiagTailX0RatChunk001Sub001Block024Tail surrogateDiagTailX0RatChunk001Sub001Block024
  ring

def SurrogateDiagonalTailChunk001Sub001Block024HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block024HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block024Head

def SurrogateDiagonalTailChunk001Sub001Block024MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block024MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block024Mid

def SurrogateDiagonalTailChunk001Sub001Block024TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block024TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block024Tail

theorem surrogateDiagonalTailChunk001Sub001Block024_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block024HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block024MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block024TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block024Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block024 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block024HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block024MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block024TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block024Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block024_eq_head_add_mid_add_tail

/-- Block 025 covers tail-support indices [15625,15650) and q from 25753 to 25793. -/

def TailChunk001Sub001Block025Part000SupportExplicit : Finset ℕ :=
  ([25753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part000 : ℚ :=
  (1881261456025 : ℚ) / 424965112271841558528

def SurrogateDiagonalTailChunk001Sub001Block025Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25753
    = surrogateDiagTailX0RatChunk001Sub001Block025Part000

theorem surrogateDiagonalTailChunk001Sub001Block025Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part000] using hcert

def TailChunk001Sub001Block025Part001SupportExplicit : Finset ℕ :=
  ([25754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part001 : ℚ :=
  (558533963075 : ℚ) / 3541545475086805056

def SurrogateDiagonalTailChunk001Sub001Block025Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25754
    = surrogateDiagTailX0RatChunk001Sub001Block025Part001

theorem surrogateDiagonalTailChunk001Sub001Block025Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part001] using hcert

def TailChunk001Sub001Block025Part002SupportExplicit : Finset ℕ :=
  ([25755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part002 : ℚ :=
  (4944287497 : ℚ) / 268489143091200000

def SurrogateDiagonalTailChunk001Sub001Block025Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25755
    = surrogateDiagTailX0RatChunk001Sub001Block025Part002

theorem surrogateDiagonalTailChunk001Sub001Block025Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part002] using hcert

def TailChunk001Sub001Block025Part003SupportExplicit : Finset ℕ :=
  ([25757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part003 : ℚ :=
  (609776975 : ℚ) / 2834794881723063168

def SurrogateDiagonalTailChunk001Sub001Block025Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25757
    = surrogateDiagTailX0RatChunk001Sub001Block025Part003

theorem surrogateDiagonalTailChunk001Sub001Block025Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part003] using hcert

def TailChunk001Sub001Block025Part004SupportExplicit : Finset ℕ :=
  ([25759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block025Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25759
    = surrogateDiagTailX0RatChunk001Sub001Block025Part004

theorem surrogateDiagonalTailChunk001Sub001Block025Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part004] using hcert

def TailChunk001Sub001Block025Part005SupportExplicit : Finset ℕ :=
  ([25761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part005 : ℚ :=
  (7608218359 : ℚ) / 7521910818243379200

def SurrogateDiagonalTailChunk001Sub001Block025Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25761
    = surrogateDiagTailX0RatChunk001Sub001Block025Part005

theorem surrogateDiagonalTailChunk001Sub001Block025Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part005] using hcert

def TailChunk001Sub001Block025Part006SupportExplicit : Finset ℕ :=
  ([25762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part006 : ℚ :=
  (356085408529 : ℚ) / 1874261987442000000

def SurrogateDiagonalTailChunk001Sub001Block025Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25762
    = surrogateDiagTailX0RatChunk001Sub001Block025Part006

theorem surrogateDiagonalTailChunk001Sub001Block025Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part006] using hcert

def TailChunk001Sub001Block025Part007SupportExplicit : Finset ℕ :=
  ([25763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block025Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25763
    = surrogateDiagTailX0RatChunk001Sub001Block025Part007

theorem surrogateDiagonalTailChunk001Sub001Block025Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part007] using hcert

def TailChunk001Sub001Block025Part008SupportExplicit : Finset ℕ :=
  ([25765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part008 : ℚ :=
  (553398181125 : ℚ) / 150331152475478818816

def SurrogateDiagonalTailChunk001Sub001Block025Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25765
    = surrogateDiagTailX0RatChunk001Sub001Block025Part008

theorem surrogateDiagonalTailChunk001Sub001Block025Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part008] using hcert

def TailChunk001Sub001Block025Part009SupportExplicit : Finset ℕ :=
  ([25766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part009 : ℚ :=
  (181413966233 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk001Sub001Block025Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25766
    = surrogateDiagTailX0RatChunk001Sub001Block025Part009

theorem surrogateDiagonalTailChunk001Sub001Block025Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part009] using hcert

def TailChunk001Sub001Block025Part010SupportExplicit : Finset ℕ :=
  ([25769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part010 : ℚ :=
  (3953965175 : ℚ) / 31261769646269792256

def SurrogateDiagonalTailChunk001Sub001Block025Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25769
    = surrogateDiagTailX0RatChunk001Sub001Block025Part010

theorem surrogateDiagonalTailChunk001Sub001Block025Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part010] using hcert

def TailChunk001Sub001Block025Part011SupportExplicit : Finset ℕ :=
  ([25770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part011 : ℚ :=
  (3130488349525 : ℚ) / 5550549221201707008

def SurrogateDiagonalTailChunk001Sub001Block025Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25770
    = surrogateDiagTailX0RatChunk001Sub001Block025Part011

theorem surrogateDiagonalTailChunk001Sub001Block025Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part011] using hcert

def TailChunk001Sub001Block025Part012SupportExplicit : Finset ℕ :=
  ([25771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block025Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25771
    = surrogateDiagTailX0RatChunk001Sub001Block025Part012

theorem surrogateDiagonalTailChunk001Sub001Block025Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part012] using hcert

def TailChunk001Sub001Block025Part013SupportExplicit : Finset ℕ :=
  ([25777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part013 : ℚ :=
  (33390962025 : ℚ) / 349998556646669910016

def SurrogateDiagonalTailChunk001Sub001Block025Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25777
    = surrogateDiagTailX0RatChunk001Sub001Block025Part013

theorem surrogateDiagonalTailChunk001Sub001Block025Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part013] using hcert

def TailChunk001Sub001Block025Part014SupportExplicit : Finset ℕ :=
  ([25778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part014 : ℚ :=
  (2595723765625 : ℚ) / 17246817872024596992

def SurrogateDiagonalTailChunk001Sub001Block025Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25778
    = surrogateDiagTailX0RatChunk001Sub001Block025Part014

theorem surrogateDiagonalTailChunk001Sub001Block025Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part014] using hcert

def TailChunk001Sub001Block025Part015SupportExplicit : Finset ℕ :=
  ([25779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part015 : ℚ :=
  (45186107 : ℚ) / 19676940886056960

def SurrogateDiagonalTailChunk001Sub001Block025Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25779
    = surrogateDiagTailX0RatChunk001Sub001Block025Part015

theorem surrogateDiagonalTailChunk001Sub001Block025Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part015] using hcert

def TailChunk001Sub001Block025Part016SupportExplicit : Finset ℕ :=
  ([25781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part016 : ℚ :=
  (925930734725 : ℚ) / 251024534615052140544

def SurrogateDiagonalTailChunk001Sub001Block025Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25781
    = surrogateDiagTailX0RatChunk001Sub001Block025Part016

theorem surrogateDiagonalTailChunk001Sub001Block025Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part016] using hcert

def TailChunk001Sub001Block025Part017SupportExplicit : Finset ℕ :=
  ([25782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part017 : ℚ :=
  (4614528570325 : ℚ) / 13627115355673755648

def SurrogateDiagonalTailChunk001Sub001Block025Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25782
    = surrogateDiagTailX0RatChunk001Sub001Block025Part017

theorem surrogateDiagonalTailChunk001Sub001Block025Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part017] using hcert

def TailChunk001Sub001Block025Part018SupportExplicit : Finset ℕ :=
  ([25783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part018 : ℚ :=
  (814824049225 : ℚ) / 695856321341562636288

def SurrogateDiagonalTailChunk001Sub001Block025Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25783
    = surrogateDiagTailX0RatChunk001Sub001Block025Part018

theorem surrogateDiagonalTailChunk001Sub001Block025Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part018] using hcert

def TailChunk001Sub001Block025Part019SupportExplicit : Finset ℕ :=
  ([25786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part019 : ℚ :=
  (2597335140625 : ℚ) / 17268239161631438112

def SurrogateDiagonalTailChunk001Sub001Block025Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25786
    = surrogateDiagTailX0RatChunk001Sub001Block025Part019

theorem surrogateDiagonalTailChunk001Sub001Block025Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part019] using hcert

def TailChunk001Sub001Block025Part020SupportExplicit : Finset ℕ :=
  ([25787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part020 : ℚ :=
  (1086121213 : ℚ) / 10473583194803404800

def SurrogateDiagonalTailChunk001Sub001Block025Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25787
    = surrogateDiagTailX0RatChunk001Sub001Block025Part020

theorem surrogateDiagonalTailChunk001Sub001Block025Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part020] using hcert

def TailChunk001Sub001Block025Part021SupportExplicit : Finset ℕ :=
  ([25789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part021 : ℚ :=
  (3039110749 : ℚ) / 2818491628514181120

def SurrogateDiagonalTailChunk001Sub001Block025Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25789
    = surrogateDiagTailX0RatChunk001Sub001Block025Part021

theorem surrogateDiagonalTailChunk001Sub001Block025Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part021] using hcert

def TailChunk001Sub001Block025Part022SupportExplicit : Finset ℕ :=
  ([25790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part022 : ℚ :=
  (7063379239225 : ℚ) / 28274730637800327168

def SurrogateDiagonalTailChunk001Sub001Block025Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25790
    = surrogateDiagTailX0RatChunk001Sub001Block025Part022

theorem surrogateDiagonalTailChunk001Sub001Block025Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part022] using hcert

def TailChunk001Sub001Block025Part023SupportExplicit : Finset ℕ :=
  ([25791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part023 : ℚ :=
  (125025 : ℚ) / 43679294415669248

def SurrogateDiagonalTailChunk001Sub001Block025Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25791
    = surrogateDiagTailX0RatChunk001Sub001Block025Part023

theorem surrogateDiagonalTailChunk001Sub001Block025Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part023] using hcert

def TailChunk001Sub001Block025Part024SupportExplicit : Finset ℕ :=
  ([25793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block025Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block025Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25793
    = surrogateDiagTailX0RatChunk001Sub001Block025Part024

theorem surrogateDiagonalTailChunk001Sub001Block025Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block025Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block025Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block025Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block025Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block025Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block025HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block025Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block025Part000
    + surrogateDiagTailX0RatChunk001Sub001Block025Part001
    + surrogateDiagTailX0RatChunk001Sub001Block025Part002
    + surrogateDiagTailX0RatChunk001Sub001Block025Part003
    + surrogateDiagTailX0RatChunk001Sub001Block025Part004
    + surrogateDiagTailX0RatChunk001Sub001Block025Part005
    + surrogateDiagTailX0RatChunk001Sub001Block025Part006
    + surrogateDiagTailX0RatChunk001Sub001Block025Part007
    + surrogateDiagTailX0RatChunk001Sub001Block025Part008
    + surrogateDiagTailX0RatChunk001Sub001Block025Part009

def surrogateDiagonalTailChunk001Sub001Block025MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block025Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block025Part010
    + surrogateDiagTailX0RatChunk001Sub001Block025Part011
    + surrogateDiagTailX0RatChunk001Sub001Block025Part012
    + surrogateDiagTailX0RatChunk001Sub001Block025Part013
    + surrogateDiagTailX0RatChunk001Sub001Block025Part014
    + surrogateDiagTailX0RatChunk001Sub001Block025Part015
    + surrogateDiagTailX0RatChunk001Sub001Block025Part016
    + surrogateDiagTailX0RatChunk001Sub001Block025Part017
    + surrogateDiagTailX0RatChunk001Sub001Block025Part018
    + surrogateDiagTailX0RatChunk001Sub001Block025Part019

def surrogateDiagonalTailChunk001Sub001Block025TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block025Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block025Part020
    + surrogateDiagTailX0RatChunk001Sub001Block025Part021
    + surrogateDiagTailX0RatChunk001Sub001Block025Part022
    + surrogateDiagTailX0RatChunk001Sub001Block025Part023
    + surrogateDiagTailX0RatChunk001Sub001Block025Part024

def surrogateDiagonalTailChunk001Sub001Block025Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block025HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block025MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block025TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block025 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block025Part000
    + surrogateDiagTailX0RatChunk001Sub001Block025Part001
    + surrogateDiagTailX0RatChunk001Sub001Block025Part002
    + surrogateDiagTailX0RatChunk001Sub001Block025Part003
    + surrogateDiagTailX0RatChunk001Sub001Block025Part004
    + surrogateDiagTailX0RatChunk001Sub001Block025Part005
    + surrogateDiagTailX0RatChunk001Sub001Block025Part006
    + surrogateDiagTailX0RatChunk001Sub001Block025Part007
    + surrogateDiagTailX0RatChunk001Sub001Block025Part008
    + surrogateDiagTailX0RatChunk001Sub001Block025Part009
    + surrogateDiagTailX0RatChunk001Sub001Block025Part010
    + surrogateDiagTailX0RatChunk001Sub001Block025Part011
    + surrogateDiagTailX0RatChunk001Sub001Block025Part012
    + surrogateDiagTailX0RatChunk001Sub001Block025Part013
    + surrogateDiagTailX0RatChunk001Sub001Block025Part014
    + surrogateDiagTailX0RatChunk001Sub001Block025Part015
    + surrogateDiagTailX0RatChunk001Sub001Block025Part016
    + surrogateDiagTailX0RatChunk001Sub001Block025Part017
    + surrogateDiagTailX0RatChunk001Sub001Block025Part018
    + surrogateDiagTailX0RatChunk001Sub001Block025Part019
    + surrogateDiagTailX0RatChunk001Sub001Block025Part020
    + surrogateDiagTailX0RatChunk001Sub001Block025Part021
    + surrogateDiagTailX0RatChunk001Sub001Block025Part022
    + surrogateDiagTailX0RatChunk001Sub001Block025Part023
    + surrogateDiagTailX0RatChunk001Sub001Block025Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block025_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block025Head + surrogateDiagTailX0RatChunk001Sub001Block025Mid + surrogateDiagTailX0RatChunk001Sub001Block025Tail =
      surrogateDiagTailX0RatChunk001Sub001Block025 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block025Head surrogateDiagTailX0RatChunk001Sub001Block025Mid surrogateDiagTailX0RatChunk001Sub001Block025Tail surrogateDiagTailX0RatChunk001Sub001Block025
  ring

def SurrogateDiagonalTailChunk001Sub001Block025HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block025HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block025Head

def SurrogateDiagonalTailChunk001Sub001Block025MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block025MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block025Mid

def SurrogateDiagonalTailChunk001Sub001Block025TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block025TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block025Tail

theorem surrogateDiagonalTailChunk001Sub001Block025_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block025HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block025MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block025TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block025Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block025 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block025HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block025MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block025TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block025Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block025_eq_head_add_mid_add_tail

/-- Block 026 covers tail-support indices [15650,15675) and q from 25795 to 25834. -/

def TailChunk001Sub001Block026Part000SupportExplicit : Finset ℕ :=
  ([25795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part000 : ℚ :=
  (49555219853 : ℚ) / 3148310541769113600

def SurrogateDiagonalTailChunk001Sub001Block026Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25795
    = surrogateDiagTailX0RatChunk001Sub001Block026Part000

theorem surrogateDiagonalTailChunk001Sub001Block026Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part000] using hcert

def TailChunk001Sub001Block026Part001SupportExplicit : Finset ℕ :=
  ([25797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part001 : ℚ :=
  (41675 : ℚ) / 14573319804706176

def SurrogateDiagonalTailChunk001Sub001Block026Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25797
    = surrogateDiagTailX0RatChunk001Sub001Block026Part001

theorem surrogateDiagonalTailChunk001Sub001Block026Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part001] using hcert

def TailChunk001Sub001Block026Part002SupportExplicit : Finset ℕ :=
  ([25798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part002 : ℚ :=
  (2599753140625 : ℚ) / 17300408503214688402

def SurrogateDiagonalTailChunk001Sub001Block026Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25798
    = surrogateDiagTailX0RatChunk001Sub001Block026Part002

theorem surrogateDiagonalTailChunk001Sub001Block026Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part002] using hcert

def TailChunk001Sub001Block026Part003SupportExplicit : Finset ℕ :=
  ([25799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block026Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25799
    = surrogateDiagTailX0RatChunk001Sub001Block026Part003

theorem surrogateDiagonalTailChunk001Sub001Block026Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part003] using hcert

def TailChunk001Sub001Block026Part004SupportExplicit : Finset ℕ :=
  ([25801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block026Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25801
    = surrogateDiagTailX0RatChunk001Sub001Block026Part004

theorem surrogateDiagonalTailChunk001Sub001Block026Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part004] using hcert

def TailChunk001Sub001Block026Part005SupportExplicit : Finset ℕ :=
  ([25802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part005 : ℚ :=
  (7274143491175 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub001Block026Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25802
    = surrogateDiagTailX0RatChunk001Sub001Block026Part005

theorem surrogateDiagonalTailChunk001Sub001Block026Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part005] using hcert

def TailChunk001Sub001Block026Part006SupportExplicit : Finset ℕ :=
  ([25805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part006 : ℚ :=
  (1984957508125 : ℚ) / 326416836970621698048

def SurrogateDiagonalTailChunk001Sub001Block026Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25805
    = surrogateDiagTailX0RatChunk001Sub001Block026Part006

theorem surrogateDiagonalTailChunk001Sub001Block026Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part006] using hcert

def TailChunk001Sub001Block026Part007SupportExplicit : Finset ℕ :=
  ([25806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part007 : ℚ :=
  (139078383739 : ℚ) / 245684346499891200

def SurrogateDiagonalTailChunk001Sub001Block026Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25806
    = surrogateDiagTailX0RatChunk001Sub001Block026Part007

theorem surrogateDiagonalTailChunk001Sub001Block026Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part007] using hcert

def TailChunk001Sub001Block026Part008SupportExplicit : Finset ℕ :=
  ([25807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part008 : ℚ :=
  (1335877989 : ℚ) / 14052813743553894400

def SurrogateDiagonalTailChunk001Sub001Block026Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25807
    = surrogateDiagTailX0RatChunk001Sub001Block026Part008

theorem surrogateDiagonalTailChunk001Sub001Block026Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part008] using hcert

def TailChunk001Sub001Block026Part009SupportExplicit : Finset ℕ :=
  ([25809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part009 : ℚ :=
  (663605255275 : ℚ) / 117908553177467486208

def SurrogateDiagonalTailChunk001Sub001Block026Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25809
    = surrogateDiagTailX0RatChunk001Sub001Block026Part009

theorem surrogateDiagonalTailChunk001Sub001Block026Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part009] using hcert

def TailChunk001Sub001Block026Part010SupportExplicit : Finset ℕ :=
  ([25810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part010 : ℚ :=
  (274344696225 : ℚ) / 983146859910397952

def SurrogateDiagonalTailChunk001Sub001Block026Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25810
    = surrogateDiagTailX0RatChunk001Sub001Block026Part010

theorem surrogateDiagonalTailChunk001Sub001Block026Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part010] using hcert

def TailChunk001Sub001Block026Part011SupportExplicit : Finset ℕ :=
  ([25811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part011 : ℚ :=
  (40928920375 : ℚ) / 254991274206249964032

def SurrogateDiagonalTailChunk001Sub001Block026Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25811
    = surrogateDiagTailX0RatChunk001Sub001Block026Part011

theorem surrogateDiagonalTailChunk001Sub001Block026Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part011] using hcert

def TailChunk001Sub001Block026Part012SupportExplicit : Finset ℕ :=
  ([25813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part012 : ℚ :=
  (485360947 : ℚ) / 4176274487049433920

def SurrogateDiagonalTailChunk001Sub001Block026Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25813
    = surrogateDiagTailX0RatChunk001Sub001Block026Part012

theorem surrogateDiagonalTailChunk001Sub001Block026Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part012] using hcert

def TailChunk001Sub001Block026Part013SupportExplicit : Finset ℕ :=
  ([25814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part013 : ℚ :=
  (2602978890625 : ℚ) / 17343370850390773362

def SurrogateDiagonalTailChunk001Sub001Block026Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25814
    = surrogateDiagTailX0RatChunk001Sub001Block026Part013

theorem surrogateDiagonalTailChunk001Sub001Block026Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part013] using hcert

def TailChunk001Sub001Block026Part014SupportExplicit : Finset ℕ :=
  ([25815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part014 : ℚ :=
  (11121221287 : ℚ) / 896397412977868800

def SurrogateDiagonalTailChunk001Sub001Block026Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25815
    = surrogateDiagTailX0RatChunk001Sub001Block026Part014

theorem surrogateDiagonalTailChunk001Sub001Block026Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part014] using hcert

def TailChunk001Sub001Block026Part015SupportExplicit : Finset ℕ :=
  ([25817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part015 : ℚ :=
  (287897741 : ℚ) / 315593208193934700

def SurrogateDiagonalTailChunk001Sub001Block026Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25817
    = surrogateDiagTailX0RatChunk001Sub001Block026Part015

theorem surrogateDiagonalTailChunk001Sub001Block026Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part015] using hcert

def TailChunk001Sub001Block026Part016SupportExplicit : Finset ℕ :=
  ([25818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part016 : ℚ :=
  (18243179167 : ℚ) / 43726535302348800

def SurrogateDiagonalTailChunk001Sub001Block026Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25818
    = surrogateDiagTailX0RatChunk001Sub001Block026Part016

theorem surrogateDiagonalTailChunk001Sub001Block026Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part016] using hcert

def TailChunk001Sub001Block026Part017SupportExplicit : Finset ℕ :=
  ([25819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block026Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25819
    = surrogateDiagTailX0RatChunk001Sub001Block026Part017

theorem surrogateDiagonalTailChunk001Sub001Block026Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part017] using hcert

def TailChunk001Sub001Block026Part018SupportExplicit : Finset ℕ :=
  ([25822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part018 : ℚ :=
  (4167348025 : ℚ) / 27783811208721522

def SurrogateDiagonalTailChunk001Sub001Block026Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25822
    = surrogateDiagTailX0RatChunk001Sub001Block026Part018

theorem surrogateDiagonalTailChunk001Sub001Block026Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part018] using hcert

def TailChunk001Sub001Block026Part019SupportExplicit : Finset ℕ :=
  ([25826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part019 : ℚ :=
  (4960077747275 : ℚ) / 30798094134917873664

def SurrogateDiagonalTailChunk001Sub001Block026Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25826
    = surrogateDiagTailX0RatChunk001Sub001Block026Part019

theorem surrogateDiagonalTailChunk001Sub001Block026Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part019] using hcert

def TailChunk001Sub001Block026Part020SupportExplicit : Finset ℕ :=
  ([25827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part020 : ℚ :=
  (125025 : ℚ) / 43923710482055168

def SurrogateDiagonalTailChunk001Sub001Block026Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25827
    = surrogateDiagTailX0RatChunk001Sub001Block026Part020

theorem surrogateDiagonalTailChunk001Sub001Block026Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part020] using hcert

def TailChunk001Sub001Block026Part021SupportExplicit : Finset ℕ :=
  ([25829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part021 : ℚ :=
  (53566202125 : ℚ) / 154716901576885441728

def SurrogateDiagonalTailChunk001Sub001Block026Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25829
    = surrogateDiagTailX0RatChunk001Sub001Block026Part021

theorem surrogateDiagonalTailChunk001Sub001Block026Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part021] using hcert

def TailChunk001Sub001Block026Part022SupportExplicit : Finset ℕ :=
  ([25831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part022 : ℚ :=
  (5804640275 : ℚ) / 6301716336247479696

def SurrogateDiagonalTailChunk001Sub001Block026Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25831
    = surrogateDiagTailX0RatChunk001Sub001Block026Part022

theorem surrogateDiagonalTailChunk001Sub001Block026Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part022] using hcert

def TailChunk001Sub001Block026Part023SupportExplicit : Finset ℕ :=
  ([25833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part023 : ℚ :=
  (897538175 : ℚ) / 1574020211149691136

def SurrogateDiagonalTailChunk001Sub001Block026Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25833
    = surrogateDiagTailX0RatChunk001Sub001Block026Part023

theorem surrogateDiagonalTailChunk001Sub001Block026Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part023] using hcert

def TailChunk001Sub001Block026Part024SupportExplicit : Finset ℕ :=
  ([25834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block026Part024 : ℚ :=
  (2607013890625 : ℚ) / 17397186249738607392

def SurrogateDiagonalTailChunk001Sub001Block026Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25834
    = surrogateDiagTailX0RatChunk001Sub001Block026Part024

theorem surrogateDiagonalTailChunk001Sub001Block026Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block026Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block026Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block026Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block026Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block026Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block026HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block026Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block026Part000
    + surrogateDiagTailX0RatChunk001Sub001Block026Part001
    + surrogateDiagTailX0RatChunk001Sub001Block026Part002
    + surrogateDiagTailX0RatChunk001Sub001Block026Part003
    + surrogateDiagTailX0RatChunk001Sub001Block026Part004
    + surrogateDiagTailX0RatChunk001Sub001Block026Part005
    + surrogateDiagTailX0RatChunk001Sub001Block026Part006
    + surrogateDiagTailX0RatChunk001Sub001Block026Part007
    + surrogateDiagTailX0RatChunk001Sub001Block026Part008
    + surrogateDiagTailX0RatChunk001Sub001Block026Part009

def surrogateDiagonalTailChunk001Sub001Block026MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block026Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block026Part010
    + surrogateDiagTailX0RatChunk001Sub001Block026Part011
    + surrogateDiagTailX0RatChunk001Sub001Block026Part012
    + surrogateDiagTailX0RatChunk001Sub001Block026Part013
    + surrogateDiagTailX0RatChunk001Sub001Block026Part014
    + surrogateDiagTailX0RatChunk001Sub001Block026Part015
    + surrogateDiagTailX0RatChunk001Sub001Block026Part016
    + surrogateDiagTailX0RatChunk001Sub001Block026Part017
    + surrogateDiagTailX0RatChunk001Sub001Block026Part018
    + surrogateDiagTailX0RatChunk001Sub001Block026Part019

def surrogateDiagonalTailChunk001Sub001Block026TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block026Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block026Part020
    + surrogateDiagTailX0RatChunk001Sub001Block026Part021
    + surrogateDiagTailX0RatChunk001Sub001Block026Part022
    + surrogateDiagTailX0RatChunk001Sub001Block026Part023
    + surrogateDiagTailX0RatChunk001Sub001Block026Part024

def surrogateDiagonalTailChunk001Sub001Block026Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block026HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block026MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block026TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block026 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block026Part000
    + surrogateDiagTailX0RatChunk001Sub001Block026Part001
    + surrogateDiagTailX0RatChunk001Sub001Block026Part002
    + surrogateDiagTailX0RatChunk001Sub001Block026Part003
    + surrogateDiagTailX0RatChunk001Sub001Block026Part004
    + surrogateDiagTailX0RatChunk001Sub001Block026Part005
    + surrogateDiagTailX0RatChunk001Sub001Block026Part006
    + surrogateDiagTailX0RatChunk001Sub001Block026Part007
    + surrogateDiagTailX0RatChunk001Sub001Block026Part008
    + surrogateDiagTailX0RatChunk001Sub001Block026Part009
    + surrogateDiagTailX0RatChunk001Sub001Block026Part010
    + surrogateDiagTailX0RatChunk001Sub001Block026Part011
    + surrogateDiagTailX0RatChunk001Sub001Block026Part012
    + surrogateDiagTailX0RatChunk001Sub001Block026Part013
    + surrogateDiagTailX0RatChunk001Sub001Block026Part014
    + surrogateDiagTailX0RatChunk001Sub001Block026Part015
    + surrogateDiagTailX0RatChunk001Sub001Block026Part016
    + surrogateDiagTailX0RatChunk001Sub001Block026Part017
    + surrogateDiagTailX0RatChunk001Sub001Block026Part018
    + surrogateDiagTailX0RatChunk001Sub001Block026Part019
    + surrogateDiagTailX0RatChunk001Sub001Block026Part020
    + surrogateDiagTailX0RatChunk001Sub001Block026Part021
    + surrogateDiagTailX0RatChunk001Sub001Block026Part022
    + surrogateDiagTailX0RatChunk001Sub001Block026Part023
    + surrogateDiagTailX0RatChunk001Sub001Block026Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block026_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block026Head + surrogateDiagTailX0RatChunk001Sub001Block026Mid + surrogateDiagTailX0RatChunk001Sub001Block026Tail =
      surrogateDiagTailX0RatChunk001Sub001Block026 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block026Head surrogateDiagTailX0RatChunk001Sub001Block026Mid surrogateDiagTailX0RatChunk001Sub001Block026Tail surrogateDiagTailX0RatChunk001Sub001Block026
  ring

def SurrogateDiagonalTailChunk001Sub001Block026HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block026HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block026Head

def SurrogateDiagonalTailChunk001Sub001Block026MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block026MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block026Mid

def SurrogateDiagonalTailChunk001Sub001Block026TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block026TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block026Tail

theorem surrogateDiagonalTailChunk001Sub001Block026_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block026HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block026MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block026TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block026Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block026 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block026HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block026MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block026TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block026Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block026_eq_head_add_mid_add_tail

/-- Block 027 covers tail-support indices [15675,15700) and q from 25835 to 25873. -/

def TailChunk001Sub001Block027Part000SupportExplicit : Finset ℕ :=
  ([25835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part000 : ℚ :=
  (1669222791625 : ℚ) / 455915577844599441408

def SurrogateDiagonalTailChunk001Sub001Block027Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25835
    = surrogateDiagTailX0RatChunk001Sub001Block027Part000

theorem surrogateDiagonalTailChunk001Sub001Block027Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part000] using hcert

def TailChunk001Sub001Block027Part001SupportExplicit : Finset ℕ :=
  ([25837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part001 : ℚ :=
  (34115247373 : ℚ) / 24032409546421123200

def SurrogateDiagonalTailChunk001Sub001Block027Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25837
    = surrogateDiagTailX0RatChunk001Sub001Block027Part001

theorem surrogateDiagonalTailChunk001Sub001Block027Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part001] using hcert

def TailChunk001Sub001Block027Part002SupportExplicit : Finset ℕ :=
  ([25838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part002 : ℚ :=
  (2607821265625 : ℚ) / 17407964340486369522

def SurrogateDiagonalTailChunk001Sub001Block027Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25838
    = surrogateDiagTailX0RatChunk001Sub001Block027Part002

theorem surrogateDiagonalTailChunk001Sub001Block027Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part002] using hcert

def TailChunk001Sub001Block027Part003SupportExplicit : Finset ℕ :=
  ([25841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block027Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25841
    = surrogateDiagTailX0RatChunk001Sub001Block027Part003

theorem surrogateDiagonalTailChunk001Sub001Block027Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part003] using hcert

def TailChunk001Sub001Block027Part004SupportExplicit : Finset ℕ :=
  ([25842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part004 : ℚ :=
  (277359141025 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk001Sub001Block027Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25842
    = surrogateDiagTailX0RatChunk001Sub001Block027Part004

theorem surrogateDiagonalTailChunk001Sub001Block027Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part004] using hcert

def TailChunk001Sub001Block027Part005SupportExplicit : Finset ℕ :=
  ([25843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part005 : ℚ :=
  (319077473 : ℚ) / 1493912802816000000

def SurrogateDiagonalTailChunk001Sub001Block027Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25843
    = surrogateDiagTailX0RatChunk001Sub001Block027Part005

theorem surrogateDiagonalTailChunk001Sub001Block027Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part005] using hcert

def TailChunk001Sub001Block027Part006SupportExplicit : Finset ℕ :=
  ([25845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part006 : ℚ :=
  (139338018125 : ℚ) / 11257174761595047936

def SurrogateDiagonalTailChunk001Sub001Block027Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25845
    = surrogateDiagTailX0RatChunk001Sub001Block027Part006

theorem surrogateDiagonalTailChunk001Sub001Block027Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part006] using hcert

def TailChunk001Sub001Block027Part007SupportExplicit : Finset ℕ :=
  ([25846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part007 : ℚ :=
  (2609436390625 : ℚ) / 17429535545261448882

def SurrogateDiagonalTailChunk001Sub001Block027Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25846
    = surrogateDiagTailX0RatChunk001Sub001Block027Part007

theorem surrogateDiagonalTailChunk001Sub001Block027Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part007] using hcert

def TailChunk001Sub001Block027Part008SupportExplicit : Finset ℕ :=
  ([25847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block027Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25847
    = surrogateDiagTailX0RatChunk001Sub001Block027Part008

theorem surrogateDiagonalTailChunk001Sub001Block027Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part008] using hcert

def TailChunk001Sub001Block027Part009SupportExplicit : Finset ℕ :=
  ([25849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block027Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25849
    = surrogateDiagTailX0RatChunk001Sub001Block027Part009

theorem surrogateDiagonalTailChunk001Sub001Block027Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part009] using hcert

def TailChunk001Sub001Block027Part010SupportExplicit : Finset ℕ :=
  ([25851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part010 : ℚ :=
  (26630254957 : ℚ) / 4747142626453555200

def SurrogateDiagonalTailChunk001Sub001Block027Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25851
    = surrogateDiagTailX0RatChunk001Sub001Block027Part010

theorem surrogateDiagonalTailChunk001Sub001Block027Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part010] using hcert

def TailChunk001Sub001Block027Part011SupportExplicit : Finset ℕ :=
  ([25853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part011 : ℚ :=
  (248194673 : ℚ) / 2487703691250000000

def SurrogateDiagonalTailChunk001Sub001Block027Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25853
    = surrogateDiagTailX0RatChunk001Sub001Block027Part011

theorem surrogateDiagonalTailChunk001Sub001Block027Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part011] using hcert

def TailChunk001Sub001Block027Part012SupportExplicit : Finset ℕ :=
  ([25854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part012 : ℚ :=
  (7624933229 : ℚ) / 20439975049574400

def SurrogateDiagonalTailChunk001Sub001Block027Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25854
    = surrogateDiagTailX0RatChunk001Sub001Block027Part012

theorem surrogateDiagonalTailChunk001Sub001Block027Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part012] using hcert

def TailChunk001Sub001Block027Part013SupportExplicit : Finset ℕ :=
  ([25855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part013 : ℚ :=
  (4458151443 : ℚ) / 1219544715996231680

def SurrogateDiagonalTailChunk001Sub001Block027Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25855
    = surrogateDiagTailX0RatChunk001Sub001Block027Part013

theorem surrogateDiagonalTailChunk001Sub001Block027Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part013] using hcert

def TailChunk001Sub001Block027Part014SupportExplicit : Finset ℕ :=
  ([25858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part014 : ℚ :=
  (506008360375 : ℚ) / 2352007295570474568

def SurrogateDiagonalTailChunk001Sub001Block027Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25858
    = surrogateDiagTailX0RatChunk001Sub001Block027Part014

theorem surrogateDiagonalTailChunk001Sub001Block027Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part014] using hcert

def TailChunk001Sub001Block027Part015SupportExplicit : Finset ℕ :=
  ([25859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part015 : ℚ :=
  (18709812373 : ℚ) / 35919683731862323200

def SurrogateDiagonalTailChunk001Sub001Block027Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25859
    = surrogateDiagTailX0RatChunk001Sub001Block027Part015

theorem surrogateDiagonalTailChunk001Sub001Block027Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part015] using hcert

def TailChunk001Sub001Block027Part016SupportExplicit : Finset ℕ :=
  ([25861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part016 : ℚ :=
  (1733255269 : ℚ) / 1906506615703125000

def SurrogateDiagonalTailChunk001Sub001Block027Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25861
    = surrogateDiagTailX0RatChunk001Sub001Block027Part016

theorem surrogateDiagonalTailChunk001Sub001Block027Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part016] using hcert

def TailChunk001Sub001Block027Part017SupportExplicit : Finset ℕ :=
  ([25862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part017 : ℚ :=
  (5057760856925 : ℚ) / 32238699947715723264

def SurrogateDiagonalTailChunk001Sub001Block027Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25862
    = surrogateDiagTailX0RatChunk001Sub001Block027Part017

theorem surrogateDiagonalTailChunk001Sub001Block027Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part017] using hcert

def TailChunk001Sub001Block027Part018SupportExplicit : Finset ℕ :=
  ([25863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part018 : ℚ :=
  (502605758725 : ℚ) / 21630485867047944192

def SurrogateDiagonalTailChunk001Sub001Block027Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25863
    = surrogateDiagTailX0RatChunk001Sub001Block027Part018

theorem surrogateDiagonalTailChunk001Sub001Block027Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part018] using hcert

def TailChunk001Sub001Block027Part019SupportExplicit : Finset ℕ :=
  ([25865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part019 : ℚ :=
  (487003592275 : ℚ) / 61522968438838075392

def SurrogateDiagonalTailChunk001Sub001Block027Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25865
    = surrogateDiagTailX0RatChunk001Sub001Block027Part019

theorem surrogateDiagonalTailChunk001Sub001Block027Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part019] using hcert

def TailChunk001Sub001Block027Part020SupportExplicit : Finset ℕ :=
  ([25867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block027Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25867
    = surrogateDiagTailX0RatChunk001Sub001Block027Part020

theorem surrogateDiagonalTailChunk001Sub001Block027Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part020] using hcert

def TailChunk001Sub001Block027Part021SupportExplicit : Finset ℕ :=
  ([25869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part021 : ℚ :=
  (2323402610975 : ℚ) / 110547498566006581824

def SurrogateDiagonalTailChunk001Sub001Block027Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25869
    = surrogateDiagTailX0RatChunk001Sub001Block027Part021

theorem surrogateDiagonalTailChunk001Sub001Block027Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part021] using hcert

def TailChunk001Sub001Block027Part022SupportExplicit : Finset ℕ :=
  ([25870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part022 : ℚ :=
  (3108464455025 : ℚ) / 10200526155331928064

def SurrogateDiagonalTailChunk001Sub001Block027Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25870
    = surrogateDiagTailX0RatChunk001Sub001Block027Part022

theorem surrogateDiagonalTailChunk001Sub001Block027Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part022] using hcert

def TailChunk001Sub001Block027Part023SupportExplicit : Finset ℕ :=
  ([25871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part023 : ℚ :=
  (561807929 : ℚ) / 2689043045068800000

def SurrogateDiagonalTailChunk001Sub001Block027Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25871
    = surrogateDiagTailX0RatChunk001Sub001Block027Part023

theorem surrogateDiagonalTailChunk001Sub001Block027Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part023] using hcert

def TailChunk001Sub001Block027Part024SupportExplicit : Finset ℕ :=
  ([25873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block027Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block027Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25873
    = surrogateDiagTailX0RatChunk001Sub001Block027Part024

theorem surrogateDiagonalTailChunk001Sub001Block027Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block027Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block027Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block027Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block027Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block027Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block027HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block027Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block027Part000
    + surrogateDiagTailX0RatChunk001Sub001Block027Part001
    + surrogateDiagTailX0RatChunk001Sub001Block027Part002
    + surrogateDiagTailX0RatChunk001Sub001Block027Part003
    + surrogateDiagTailX0RatChunk001Sub001Block027Part004
    + surrogateDiagTailX0RatChunk001Sub001Block027Part005
    + surrogateDiagTailX0RatChunk001Sub001Block027Part006
    + surrogateDiagTailX0RatChunk001Sub001Block027Part007
    + surrogateDiagTailX0RatChunk001Sub001Block027Part008
    + surrogateDiagTailX0RatChunk001Sub001Block027Part009

def surrogateDiagonalTailChunk001Sub001Block027MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block027Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block027Part010
    + surrogateDiagTailX0RatChunk001Sub001Block027Part011
    + surrogateDiagTailX0RatChunk001Sub001Block027Part012
    + surrogateDiagTailX0RatChunk001Sub001Block027Part013
    + surrogateDiagTailX0RatChunk001Sub001Block027Part014
    + surrogateDiagTailX0RatChunk001Sub001Block027Part015
    + surrogateDiagTailX0RatChunk001Sub001Block027Part016
    + surrogateDiagTailX0RatChunk001Sub001Block027Part017
    + surrogateDiagTailX0RatChunk001Sub001Block027Part018
    + surrogateDiagTailX0RatChunk001Sub001Block027Part019

def surrogateDiagonalTailChunk001Sub001Block027TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block027Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block027Part020
    + surrogateDiagTailX0RatChunk001Sub001Block027Part021
    + surrogateDiagTailX0RatChunk001Sub001Block027Part022
    + surrogateDiagTailX0RatChunk001Sub001Block027Part023
    + surrogateDiagTailX0RatChunk001Sub001Block027Part024

def surrogateDiagonalTailChunk001Sub001Block027Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block027HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block027MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block027TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block027 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block027Part000
    + surrogateDiagTailX0RatChunk001Sub001Block027Part001
    + surrogateDiagTailX0RatChunk001Sub001Block027Part002
    + surrogateDiagTailX0RatChunk001Sub001Block027Part003
    + surrogateDiagTailX0RatChunk001Sub001Block027Part004
    + surrogateDiagTailX0RatChunk001Sub001Block027Part005
    + surrogateDiagTailX0RatChunk001Sub001Block027Part006
    + surrogateDiagTailX0RatChunk001Sub001Block027Part007
    + surrogateDiagTailX0RatChunk001Sub001Block027Part008
    + surrogateDiagTailX0RatChunk001Sub001Block027Part009
    + surrogateDiagTailX0RatChunk001Sub001Block027Part010
    + surrogateDiagTailX0RatChunk001Sub001Block027Part011
    + surrogateDiagTailX0RatChunk001Sub001Block027Part012
    + surrogateDiagTailX0RatChunk001Sub001Block027Part013
    + surrogateDiagTailX0RatChunk001Sub001Block027Part014
    + surrogateDiagTailX0RatChunk001Sub001Block027Part015
    + surrogateDiagTailX0RatChunk001Sub001Block027Part016
    + surrogateDiagTailX0RatChunk001Sub001Block027Part017
    + surrogateDiagTailX0RatChunk001Sub001Block027Part018
    + surrogateDiagTailX0RatChunk001Sub001Block027Part019
    + surrogateDiagTailX0RatChunk001Sub001Block027Part020
    + surrogateDiagTailX0RatChunk001Sub001Block027Part021
    + surrogateDiagTailX0RatChunk001Sub001Block027Part022
    + surrogateDiagTailX0RatChunk001Sub001Block027Part023
    + surrogateDiagTailX0RatChunk001Sub001Block027Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block027_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block027Head + surrogateDiagTailX0RatChunk001Sub001Block027Mid + surrogateDiagTailX0RatChunk001Sub001Block027Tail =
      surrogateDiagTailX0RatChunk001Sub001Block027 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block027Head surrogateDiagTailX0RatChunk001Sub001Block027Mid surrogateDiagTailX0RatChunk001Sub001Block027Tail surrogateDiagTailX0RatChunk001Sub001Block027
  ring

def SurrogateDiagonalTailChunk001Sub001Block027HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block027HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block027Head

def SurrogateDiagonalTailChunk001Sub001Block027MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block027MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block027Mid

def SurrogateDiagonalTailChunk001Sub001Block027TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block027TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block027Tail

theorem surrogateDiagonalTailChunk001Sub001Block027_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block027HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block027MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block027TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block027Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block027 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block027HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block027MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block027TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block027Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block027_eq_head_add_mid_add_tail

/-- Block 028 covers tail-support indices [15700,15725) and q from 25874 to 25914. -/

def TailChunk001Sub001Block028Part000SupportExplicit : Finset ℕ :=
  ([25874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part000 : ℚ :=
  (377123629717 : ℚ) / 2186860851049267200

def SurrogateDiagonalTailChunk001Sub001Block028Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25874
    = surrogateDiagTailX0RatChunk001Sub001Block028Part000

theorem surrogateDiagonalTailChunk001Sub001Block028Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part000] using hcert

def TailChunk001Sub001Block028Part001SupportExplicit : Finset ℕ :=
  ([25877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part001 : ℚ :=
  (106759852225 : ℚ) / 1063257212932281335808

def SurrogateDiagonalTailChunk001Sub001Block028Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25877
    = surrogateDiagTailX0RatChunk001Sub001Block028Part001

theorem surrogateDiagonalTailChunk001Sub001Block028Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part001] using hcert

def TailChunk001Sub001Block028Part002SupportExplicit : Finset ℕ :=
  ([25878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part002 : ℚ :=
  (884119350275 : ℚ) / 1826078184564231168

def SurrogateDiagonalTailChunk001Sub001Block028Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25878
    = surrogateDiagTailX0RatChunk001Sub001Block028Part002

theorem surrogateDiagonalTailChunk001Sub001Block028Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part002] using hcert

def TailChunk001Sub001Block028Part003SupportExplicit : Finset ℕ :=
  ([25879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part003 : ℚ :=
  (855650934625 : ℚ) / 604727488863011340288

def SurrogateDiagonalTailChunk001Sub001Block028Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25879
    = surrogateDiagTailX0RatChunk001Sub001Block028Part003

theorem surrogateDiagonalTailChunk001Sub001Block028Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part003] using hcert

def TailChunk001Sub001Block028Part004SupportExplicit : Finset ℕ :=
  ([25881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part004 : ℚ :=
  (2325558610925 : ℚ) / 110752786344670845504

def SurrogateDiagonalTailChunk001Sub001Block028Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25881
    = surrogateDiagTailX0RatChunk001Sub001Block028Part004

theorem surrogateDiagonalTailChunk001Sub001Block028Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part004] using hcert

def TailChunk001Sub001Block028Part005SupportExplicit : Finset ℕ :=
  ([25882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part005 : ℚ :=
  (4186737025 : ℚ) / 28042966652796192

def SurrogateDiagonalTailChunk001Sub001Block028Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25882
    = surrogateDiagTailX0RatChunk001Sub001Block028Part005

theorem surrogateDiagonalTailChunk001Sub001Block028Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part005] using hcert

def TailChunk001Sub001Block028Part006SupportExplicit : Finset ℕ :=
  ([25883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part006 : ℚ :=
  (21487133357 : ℚ) / 10886088462336000000

def SurrogateDiagonalTailChunk001Sub001Block028Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25883
    = surrogateDiagTailX0RatChunk001Sub001Block028Part006

theorem surrogateDiagonalTailChunk001Sub001Block028Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part006] using hcert

def TailChunk001Sub001Block028Part007SupportExplicit : Finset ℕ :=
  ([25885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part007 : ℚ :=
  (71651277727 : ℚ) / 15748681014477619200

def SurrogateDiagonalTailChunk001Sub001Block028Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25885
    = surrogateDiagTailX0RatChunk001Sub001Block028Part007

theorem surrogateDiagonalTailChunk001Sub001Block028Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part007] using hcert

def TailChunk001Sub001Block028Part008SupportExplicit : Finset ℕ :=
  ([25887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part008 : ℚ :=
  (581659246475 : ℚ) / 27713884346552883456

def SurrogateDiagonalTailChunk001Sub001Block028Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25887
    = surrogateDiagTailX0RatChunk001Sub001Block028Part008

theorem surrogateDiagonalTailChunk001Sub001Block028Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part008] using hcert

def TailChunk001Sub001Block028Part009SupportExplicit : Finset ℕ :=
  ([25889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block028Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25889
    = surrogateDiagTailX0RatChunk001Sub001Block028Part009

theorem surrogateDiagonalTailChunk001Sub001Block028Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part009] using hcert

def TailChunk001Sub001Block028Part010SupportExplicit : Finset ℕ :=
  ([25890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part010 : ℚ :=
  (4043371176475 : ℚ) / 5654782042247036928

def SurrogateDiagonalTailChunk001Sub001Block028Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25890
    = surrogateDiagTailX0RatChunk001Sub001Block028Part010

theorem surrogateDiagonalTailChunk001Sub001Block028Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part010] using hcert

def TailChunk001Sub001Block028Part011SupportExplicit : Finset ℕ :=
  ([25891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part011 : ℚ :=
  (36597167775 : ℚ) / 73279779387807760384

def SurrogateDiagonalTailChunk001Sub001Block028Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25891
    = surrogateDiagTailX0RatChunk001Sub001Block028Part011

theorem surrogateDiagonalTailChunk001Sub001Block028Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part011] using hcert

def TailChunk001Sub001Block028Part012SupportExplicit : Finset ℕ :=
  ([25895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part012 : ℚ :=
  (1676980790125 : ℚ) / 460166510205209069568

def SurrogateDiagonalTailChunk001Sub001Block028Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25895
    = surrogateDiagTailX0RatChunk001Sub001Block028Part012

theorem surrogateDiagonalTailChunk001Sub001Block028Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part012] using hcert

def TailChunk001Sub001Block028Part013SupportExplicit : Finset ℕ :=
  ([25897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part013 : ℚ :=
  (840250102975 : ℚ) / 722404314984094138368

def SurrogateDiagonalTailChunk001Sub001Block028Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25897
    = surrogateDiagTailX0RatChunk001Sub001Block028Part013

theorem surrogateDiagonalTailChunk001Sub001Block028Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part013] using hcert

def TailChunk001Sub001Block028Part014SupportExplicit : Finset ℕ :=
  ([25898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part014 : ℚ :=
  (13713771375 : ℚ) / 4869468921815807584

def SurrogateDiagonalTailChunk001Sub001Block028Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25898
    = surrogateDiagTailX0RatChunk001Sub001Block028Part014

theorem surrogateDiagonalTailChunk001Sub001Block028Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part014] using hcert

def TailChunk001Sub001Block028Part015SupportExplicit : Finset ℕ :=
  ([25899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part015 : ℚ :=
  (4574603753725 : ℚ) / 203780424360869756928

def SurrogateDiagonalTailChunk001Sub001Block028Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25899
    = surrogateDiagTailX0RatChunk001Sub001Block028Part015

theorem surrogateDiagonalTailChunk001Sub001Block028Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part015] using hcert

def TailChunk001Sub001Block028Part016SupportExplicit : Finset ℕ :=
  ([25901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part016 : ℚ :=
  (40436104525 : ℚ) / 260360612063734892832

def SurrogateDiagonalTailChunk001Sub001Block028Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25901
    = surrogateDiagTailX0RatChunk001Sub001Block028Part016

theorem surrogateDiagonalTailChunk001Sub001Block028Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part016] using hcert

def TailChunk001Sub001Block028Part017SupportExplicit : Finset ℕ :=
  ([25903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block028Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25903
    = surrogateDiagTailX0RatChunk001Sub001Block028Part017

theorem surrogateDiagonalTailChunk001Sub001Block028Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part017] using hcert

def TailChunk001Sub001Block028Part018SupportExplicit : Finset ℕ :=
  ([25905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part018 : ℚ :=
  (71647924943 : ℚ) / 1213151936879001600

def SurrogateDiagonalTailChunk001Sub001Block028Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25905
    = surrogateDiagTailX0RatChunk001Sub001Block028Part018

theorem surrogateDiagonalTailChunk001Sub001Block028Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part018] using hcert

def TailChunk001Sub001Block028Part019SupportExplicit : Finset ℕ :=
  ([25906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block028Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25906
    = surrogateDiagTailX0RatChunk001Sub001Block028Part019

theorem surrogateDiagonalTailChunk001Sub001Block028Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part019] using hcert

def TailChunk001Sub001Block028Part020SupportExplicit : Finset ℕ :=
  ([25907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part020 : ℚ :=
  (34299997393 : ℚ) / 24293984385312000000

def SurrogateDiagonalTailChunk001Sub001Block028Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25907
    = surrogateDiagTailX0RatChunk001Sub001Block028Part020

theorem surrogateDiagonalTailChunk001Sub001Block028Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part020] using hcert

def TailChunk001Sub001Block028Part021SupportExplicit : Finset ℕ :=
  ([25909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part021 : ℚ :=
  (373733705975 : ℚ) / 408205811895259889664

def SurrogateDiagonalTailChunk001Sub001Block028Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25909
    = surrogateDiagTailX0RatChunk001Sub001Block028Part021

theorem surrogateDiagonalTailChunk001Sub001Block028Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part021] using hcert

def TailChunk001Sub001Block028Part022SupportExplicit : Finset ℕ :=
  ([25910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part022 : ℚ :=
  (33583805809 : ℚ) / 1152194696476723200

def SurrogateDiagonalTailChunk001Sub001Block028Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25910
    = surrogateDiagTailX0RatChunk001Sub001Block028Part022

theorem surrogateDiagonalTailChunk001Sub001Block028Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part022] using hcert

def TailChunk001Sub001Block028Part023SupportExplicit : Finset ℕ :=
  ([25913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block028Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25913
    = surrogateDiagTailX0RatChunk001Sub001Block028Part023

theorem surrogateDiagonalTailChunk001Sub001Block028Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part023] using hcert

def TailChunk001Sub001Block028Part024SupportExplicit : Finset ℕ :=
  ([25914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block028Part024 : ℚ :=
  (83281715225 : ℚ) / 533269390531756032

def SurrogateDiagonalTailChunk001Sub001Block028Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25914
    = surrogateDiagTailX0RatChunk001Sub001Block028Part024

theorem surrogateDiagonalTailChunk001Sub001Block028Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block028Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block028Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block028Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block028Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block028Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block028HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block028Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block028Part000
    + surrogateDiagTailX0RatChunk001Sub001Block028Part001
    + surrogateDiagTailX0RatChunk001Sub001Block028Part002
    + surrogateDiagTailX0RatChunk001Sub001Block028Part003
    + surrogateDiagTailX0RatChunk001Sub001Block028Part004
    + surrogateDiagTailX0RatChunk001Sub001Block028Part005
    + surrogateDiagTailX0RatChunk001Sub001Block028Part006
    + surrogateDiagTailX0RatChunk001Sub001Block028Part007
    + surrogateDiagTailX0RatChunk001Sub001Block028Part008
    + surrogateDiagTailX0RatChunk001Sub001Block028Part009

def surrogateDiagonalTailChunk001Sub001Block028MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block028Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block028Part010
    + surrogateDiagTailX0RatChunk001Sub001Block028Part011
    + surrogateDiagTailX0RatChunk001Sub001Block028Part012
    + surrogateDiagTailX0RatChunk001Sub001Block028Part013
    + surrogateDiagTailX0RatChunk001Sub001Block028Part014
    + surrogateDiagTailX0RatChunk001Sub001Block028Part015
    + surrogateDiagTailX0RatChunk001Sub001Block028Part016
    + surrogateDiagTailX0RatChunk001Sub001Block028Part017
    + surrogateDiagTailX0RatChunk001Sub001Block028Part018
    + surrogateDiagTailX0RatChunk001Sub001Block028Part019

def surrogateDiagonalTailChunk001Sub001Block028TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block028Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block028Part020
    + surrogateDiagTailX0RatChunk001Sub001Block028Part021
    + surrogateDiagTailX0RatChunk001Sub001Block028Part022
    + surrogateDiagTailX0RatChunk001Sub001Block028Part023
    + surrogateDiagTailX0RatChunk001Sub001Block028Part024

def surrogateDiagonalTailChunk001Sub001Block028Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block028HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block028MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block028TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block028 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block028Part000
    + surrogateDiagTailX0RatChunk001Sub001Block028Part001
    + surrogateDiagTailX0RatChunk001Sub001Block028Part002
    + surrogateDiagTailX0RatChunk001Sub001Block028Part003
    + surrogateDiagTailX0RatChunk001Sub001Block028Part004
    + surrogateDiagTailX0RatChunk001Sub001Block028Part005
    + surrogateDiagTailX0RatChunk001Sub001Block028Part006
    + surrogateDiagTailX0RatChunk001Sub001Block028Part007
    + surrogateDiagTailX0RatChunk001Sub001Block028Part008
    + surrogateDiagTailX0RatChunk001Sub001Block028Part009
    + surrogateDiagTailX0RatChunk001Sub001Block028Part010
    + surrogateDiagTailX0RatChunk001Sub001Block028Part011
    + surrogateDiagTailX0RatChunk001Sub001Block028Part012
    + surrogateDiagTailX0RatChunk001Sub001Block028Part013
    + surrogateDiagTailX0RatChunk001Sub001Block028Part014
    + surrogateDiagTailX0RatChunk001Sub001Block028Part015
    + surrogateDiagTailX0RatChunk001Sub001Block028Part016
    + surrogateDiagTailX0RatChunk001Sub001Block028Part017
    + surrogateDiagTailX0RatChunk001Sub001Block028Part018
    + surrogateDiagTailX0RatChunk001Sub001Block028Part019
    + surrogateDiagTailX0RatChunk001Sub001Block028Part020
    + surrogateDiagTailX0RatChunk001Sub001Block028Part021
    + surrogateDiagTailX0RatChunk001Sub001Block028Part022
    + surrogateDiagTailX0RatChunk001Sub001Block028Part023
    + surrogateDiagTailX0RatChunk001Sub001Block028Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block028_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block028Head + surrogateDiagTailX0RatChunk001Sub001Block028Mid + surrogateDiagTailX0RatChunk001Sub001Block028Tail =
      surrogateDiagTailX0RatChunk001Sub001Block028 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block028Head surrogateDiagTailX0RatChunk001Sub001Block028Mid surrogateDiagTailX0RatChunk001Sub001Block028Tail surrogateDiagTailX0RatChunk001Sub001Block028
  ring

def SurrogateDiagonalTailChunk001Sub001Block028HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block028HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block028Head

def SurrogateDiagonalTailChunk001Sub001Block028MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block028MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block028Mid

def SurrogateDiagonalTailChunk001Sub001Block028TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block028TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block028Tail

theorem surrogateDiagonalTailChunk001Sub001Block028_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block028HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block028MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block028TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block028Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block028 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block028HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block028MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block028TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block028Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block028_eq_head_add_mid_add_tail

/-- Block 029 covers tail-support indices [15725,15750) and q from 25915 to 25955. -/

def TailChunk001Sub001Block029Part000SupportExplicit : Finset ℕ :=
  ([25915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part000 : ℚ :=
  (23520083917 : ℚ) / 5507160156300902400

def SurrogateDiagonalTailChunk001Sub001Block029Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25915
    = surrogateDiagTailX0RatChunk001Sub001Block029Part000

theorem surrogateDiagonalTailChunk001Sub001Block029Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part000] using hcert

def TailChunk001Sub001Block029Part001SupportExplicit : Finset ℕ :=
  ([25917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part001 : ℚ :=
  (117086523425 : ℚ) / 5166015051978473472

def SurrogateDiagonalTailChunk001Sub001Block029Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25917
    = surrogateDiagTailX0RatChunk001Sub001Block029Part001

theorem surrogateDiagonalTailChunk001Sub001Block029Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part001] using hcert

def TailChunk001Sub001Block029Part002SupportExplicit : Finset ℕ :=
  ([25918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25918
    = surrogateDiagTailX0RatChunk001Sub001Block029Part002

theorem surrogateDiagonalTailChunk001Sub001Block029Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part002] using hcert

def TailChunk001Sub001Block029Part003SupportExplicit : Finset ℕ :=
  ([25919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25919
    = surrogateDiagTailX0RatChunk001Sub001Block029Part003

theorem surrogateDiagonalTailChunk001Sub001Block029Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part003] using hcert

def TailChunk001Sub001Block029Part004SupportExplicit : Finset ℕ :=
  ([25922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part004 : ℚ :=
  (34834423625 : ℚ) / 5669525165211942912

def SurrogateDiagonalTailChunk001Sub001Block029Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25922
    = surrogateDiagTailX0RatChunk001Sub001Block029Part004

theorem surrogateDiagonalTailChunk001Sub001Block029Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part004] using hcert

def TailChunk001Sub001Block029Part005SupportExplicit : Finset ℕ :=
  ([25923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part005 : ℚ :=
  (9332449943 : ℚ) / 445894183417282560

def SurrogateDiagonalTailChunk001Sub001Block029Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25923
    = surrogateDiagTailX0RatChunk001Sub001Block029Part005

theorem surrogateDiagonalTailChunk001Sub001Block029Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part005] using hcert

def TailChunk001Sub001Block029Part006SupportExplicit : Finset ℕ :=
  ([25926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part006 : ℚ :=
  (24604775175 : ℚ) / 245801535248367616

def SurrogateDiagonalTailChunk001Sub001Block029Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25926
    = surrogateDiagTailX0RatChunk001Sub001Block029Part006

theorem surrogateDiagonalTailChunk001Sub001Block029Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part006] using hcert

def TailChunk001Sub001Block029Part007SupportExplicit : Finset ℕ :=
  ([25927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part007 : ℚ :=
  (6968308999 : ℚ) / 7704208068931084800

def SurrogateDiagonalTailChunk001Sub001Block029Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25927
    = surrogateDiagTailX0RatChunk001Sub001Block029Part007

theorem surrogateDiagonalTailChunk001Sub001Block029Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part007] using hcert

def TailChunk001Sub001Block029Part008SupportExplicit : Finset ℕ :=
  ([25930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part008 : ℚ :=
  (280296795175 : ℚ) / 9631314361813303296

def SurrogateDiagonalTailChunk001Sub001Block029Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25930
    = surrogateDiagTailX0RatChunk001Sub001Block029Part008

theorem surrogateDiagonalTailChunk001Sub001Block029Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part008] using hcert

def TailChunk001Sub001Block029Part009SupportExplicit : Finset ℕ :=
  ([25931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25931
    = surrogateDiagTailX0RatChunk001Sub001Block029Part009

theorem surrogateDiagonalTailChunk001Sub001Block029Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part009] using hcert

def TailChunk001Sub001Block029Part010SupportExplicit : Finset ℕ :=
  ([25933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25933
    = surrogateDiagTailX0RatChunk001Sub001Block029Part010

theorem surrogateDiagonalTailChunk001Sub001Block029Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part010] using hcert

def TailChunk001Sub001Block029Part011SupportExplicit : Finset ℕ :=
  ([25934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25934
    = surrogateDiagTailX0RatChunk001Sub001Block029Part011

theorem surrogateDiagonalTailChunk001Sub001Block029Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part011] using hcert

def TailChunk001Sub001Block029Part012SupportExplicit : Finset ℕ :=
  ([25935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part012 : ℚ :=
  (3116102999125 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub001Block029Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25935
    = surrogateDiagTailX0RatChunk001Sub001Block029Part012

theorem surrogateDiagonalTailChunk001Sub001Block029Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part012] using hcert

def TailChunk001Sub001Block029Part013SupportExplicit : Finset ℕ :=
  ([25937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part013 : ℚ :=
  (9014342509 : ℚ) / 40335645676032000000

def SurrogateDiagonalTailChunk001Sub001Block029Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25937
    = surrogateDiagTailX0RatChunk001Sub001Block029Part013

theorem surrogateDiagonalTailChunk001Sub001Block029Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part013] using hcert

def TailChunk001Sub001Block029Part014SupportExplicit : Finset ℕ :=
  ([25939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25939
    = surrogateDiagTailX0RatChunk001Sub001Block029Part014

theorem surrogateDiagonalTailChunk001Sub001Block029Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part014] using hcert

def TailChunk001Sub001Block029Part015SupportExplicit : Finset ℕ :=
  ([25941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part015 : ℚ :=
  (2336353610675 : ℚ) / 111783517292929103424

def SurrogateDiagonalTailChunk001Sub001Block029Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25941
    = surrogateDiagTailX0RatChunk001Sub001Block029Part015

theorem surrogateDiagonalTailChunk001Sub001Block029Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part015] using hcert

def TailChunk001Sub001Block029Part016SupportExplicit : Finset ℕ :=
  ([25942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part016 : ℚ :=
  (774059773225 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub001Block029Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25942
    = surrogateDiagTailX0RatChunk001Sub001Block029Part016

theorem surrogateDiagonalTailChunk001Sub001Block029Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part016] using hcert

def TailChunk001Sub001Block029Part017SupportExplicit : Finset ℕ :=
  ([25943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25943
    = surrogateDiagTailX0RatChunk001Sub001Block029Part017

theorem surrogateDiagonalTailChunk001Sub001Block029Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part017] using hcert

def TailChunk001Sub001Block029Part018SupportExplicit : Finset ℕ :=
  ([25945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part018 : ℚ :=
  (561153179625 : ℚ) / 154577201021197582336

def SurrogateDiagonalTailChunk001Sub001Block029Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25945
    = surrogateDiagTailX0RatChunk001Sub001Block029Part018

theorem surrogateDiagonalTailChunk001Sub001Block029Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part018] using hcert

def TailChunk001Sub001Block029Part019SupportExplicit : Finset ℕ :=
  ([25946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25946
    = surrogateDiagTailX0RatChunk001Sub001Block029Part019

theorem surrogateDiagonalTailChunk001Sub001Block029Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part019] using hcert

def TailChunk001Sub001Block029Part020SupportExplicit : Finset ℕ :=
  ([25949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part020 : ℚ :=
  (3619029223 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk001Sub001Block029Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25949
    = surrogateDiagTailX0RatChunk001Sub001Block029Part020

theorem surrogateDiagonalTailChunk001Sub001Block029Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part020] using hcert

def TailChunk001Sub001Block029Part021SupportExplicit : Finset ℕ :=
  ([25951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block029Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25951
    = surrogateDiagTailX0RatChunk001Sub001Block029Part021

theorem surrogateDiagonalTailChunk001Sub001Block029Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part021] using hcert

def TailChunk001Sub001Block029Part022SupportExplicit : Finset ℕ :=
  ([25953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part022 : ℚ :=
  (91284916313 : ℚ) / 3983767474176000000

def SurrogateDiagonalTailChunk001Sub001Block029Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25953
    = surrogateDiagTailX0RatChunk001Sub001Block029Part022

theorem surrogateDiagonalTailChunk001Sub001Block029Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part022] using hcert

def TailChunk001Sub001Block029Part023SupportExplicit : Finset ℕ :=
  ([25954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part023 : ℚ :=
  (208869763525 : ℚ) / 56787712887600655488

def SurrogateDiagonalTailChunk001Sub001Block029Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25954
    = surrogateDiagTailX0RatChunk001Sub001Block029Part023

theorem surrogateDiagonalTailChunk001Sub001Block029Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part023] using hcert

def TailChunk001Sub001Block029Part024SupportExplicit : Finset ℕ :=
  ([25955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block029Part024 : ℚ :=
  (43303874475 : ℚ) / 9404369155187277824

def SurrogateDiagonalTailChunk001Sub001Block029Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25955
    = surrogateDiagTailX0RatChunk001Sub001Block029Part024

theorem surrogateDiagonalTailChunk001Sub001Block029Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block029Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block029Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block029Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block029Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block029Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block029HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block029Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block029Part000
    + surrogateDiagTailX0RatChunk001Sub001Block029Part001
    + surrogateDiagTailX0RatChunk001Sub001Block029Part002
    + surrogateDiagTailX0RatChunk001Sub001Block029Part003
    + surrogateDiagTailX0RatChunk001Sub001Block029Part004
    + surrogateDiagTailX0RatChunk001Sub001Block029Part005
    + surrogateDiagTailX0RatChunk001Sub001Block029Part006
    + surrogateDiagTailX0RatChunk001Sub001Block029Part007
    + surrogateDiagTailX0RatChunk001Sub001Block029Part008
    + surrogateDiagTailX0RatChunk001Sub001Block029Part009

def surrogateDiagonalTailChunk001Sub001Block029MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block029Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block029Part010
    + surrogateDiagTailX0RatChunk001Sub001Block029Part011
    + surrogateDiagTailX0RatChunk001Sub001Block029Part012
    + surrogateDiagTailX0RatChunk001Sub001Block029Part013
    + surrogateDiagTailX0RatChunk001Sub001Block029Part014
    + surrogateDiagTailX0RatChunk001Sub001Block029Part015
    + surrogateDiagTailX0RatChunk001Sub001Block029Part016
    + surrogateDiagTailX0RatChunk001Sub001Block029Part017
    + surrogateDiagTailX0RatChunk001Sub001Block029Part018
    + surrogateDiagTailX0RatChunk001Sub001Block029Part019

def surrogateDiagonalTailChunk001Sub001Block029TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block029Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block029Part020
    + surrogateDiagTailX0RatChunk001Sub001Block029Part021
    + surrogateDiagTailX0RatChunk001Sub001Block029Part022
    + surrogateDiagTailX0RatChunk001Sub001Block029Part023
    + surrogateDiagTailX0RatChunk001Sub001Block029Part024

def surrogateDiagonalTailChunk001Sub001Block029Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block029HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block029MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block029TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block029 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block029Part000
    + surrogateDiagTailX0RatChunk001Sub001Block029Part001
    + surrogateDiagTailX0RatChunk001Sub001Block029Part002
    + surrogateDiagTailX0RatChunk001Sub001Block029Part003
    + surrogateDiagTailX0RatChunk001Sub001Block029Part004
    + surrogateDiagTailX0RatChunk001Sub001Block029Part005
    + surrogateDiagTailX0RatChunk001Sub001Block029Part006
    + surrogateDiagTailX0RatChunk001Sub001Block029Part007
    + surrogateDiagTailX0RatChunk001Sub001Block029Part008
    + surrogateDiagTailX0RatChunk001Sub001Block029Part009
    + surrogateDiagTailX0RatChunk001Sub001Block029Part010
    + surrogateDiagTailX0RatChunk001Sub001Block029Part011
    + surrogateDiagTailX0RatChunk001Sub001Block029Part012
    + surrogateDiagTailX0RatChunk001Sub001Block029Part013
    + surrogateDiagTailX0RatChunk001Sub001Block029Part014
    + surrogateDiagTailX0RatChunk001Sub001Block029Part015
    + surrogateDiagTailX0RatChunk001Sub001Block029Part016
    + surrogateDiagTailX0RatChunk001Sub001Block029Part017
    + surrogateDiagTailX0RatChunk001Sub001Block029Part018
    + surrogateDiagTailX0RatChunk001Sub001Block029Part019
    + surrogateDiagTailX0RatChunk001Sub001Block029Part020
    + surrogateDiagTailX0RatChunk001Sub001Block029Part021
    + surrogateDiagTailX0RatChunk001Sub001Block029Part022
    + surrogateDiagTailX0RatChunk001Sub001Block029Part023
    + surrogateDiagTailX0RatChunk001Sub001Block029Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block029_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block029Head + surrogateDiagTailX0RatChunk001Sub001Block029Mid + surrogateDiagTailX0RatChunk001Sub001Block029Tail =
      surrogateDiagTailX0RatChunk001Sub001Block029 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block029Head surrogateDiagTailX0RatChunk001Sub001Block029Mid surrogateDiagTailX0RatChunk001Sub001Block029Tail surrogateDiagTailX0RatChunk001Sub001Block029
  ring

def SurrogateDiagonalTailChunk001Sub001Block029HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block029HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block029Head

def SurrogateDiagonalTailChunk001Sub001Block029MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block029MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block029Mid

def SurrogateDiagonalTailChunk001Sub001Block029TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block029TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block029Tail

theorem surrogateDiagonalTailChunk001Sub001Block029_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block029HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block029MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block029TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block029Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block029 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block029HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block029MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block029TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block029Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block029_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

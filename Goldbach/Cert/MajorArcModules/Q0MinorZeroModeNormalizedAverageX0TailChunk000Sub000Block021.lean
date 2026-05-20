import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [21,22). -/

/- Block 021 covers tail-support indices [525,550) and q from 914 to 955. -/

def TailChunk000Sub000Block021Part000SupportExplicit : Finset ℕ :=
  ([914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part000 : ℚ :=
  (143296520125 : ℚ) / 108115068930048

def SurrogateDiagonalTailChunk000Sub000Block021Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 914
    = surrogateDiagTailX0RatChunk000Sub000Block021Part000

theorem surrogateDiagonalTailChunk000Sub000Block021Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part000] using hcert

def TailChunk000Sub000Block021Part001SupportExplicit : Finset ℕ :=
  ([915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part001 : ℚ :=
  (1917185903 : ℚ) / 1769825894400

def SurrogateDiagonalTailChunk000Sub000Block021Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 915
    = surrogateDiagTailX0RatChunk000Sub000Block021Part001

theorem surrogateDiagonalTailChunk000Sub000Block021Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part001] using hcert

def TailChunk000Sub000Block021Part002SupportExplicit : Finset ℕ :=
  ([917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part002 : ℚ :=
  (1008381521 : ℚ) / 4113606556800

def SurrogateDiagonalTailChunk000Sub000Block021Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 917
    = surrogateDiagTailX0RatChunk000Sub000Block021Part002

theorem surrogateDiagonalTailChunk000Sub000Block021Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part002] using hcert

def TailChunk000Sub000Block021Part003SupportExplicit : Finset ℕ :=
  ([919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part003 : ℚ :=
  (131857086125 : ℚ) / 887907221155044

def SurrogateDiagonalTailChunk000Sub000Block021Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 919
    = surrogateDiagTailX0RatChunk000Sub000Block021Part003

theorem surrogateDiagonalTailChunk000Sub000Block021Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part003] using hcert

def TailChunk000Sub000Block021Part004SupportExplicit : Finset ℕ :=
  ([921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part004 : ℚ :=
  (99817353725 : ℚ) / 175389080721984

def SurrogateDiagonalTailChunk000Sub000Block021Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 921
    = surrogateDiagTailX0RatChunk000Sub000Block021Part004

theorem surrogateDiagonalTailChunk000Sub000Block021Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part004] using hcert

def TailChunk000Sub000Block021Part005SupportExplicit : Finset ℕ :=
  ([922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part005 : ℚ :=
  (1166527769 : ℚ) / 895670298240

def SurrogateDiagonalTailChunk000Sub000Block021Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 922
    = surrogateDiagTailX0RatChunk000Sub000Block021Part005

theorem surrogateDiagonalTailChunk000Sub000Block021Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part005] using hcert

def TailChunk000Sub000Block021Part006SupportExplicit : Finset ℕ :=
  ([923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part006 : ℚ :=
  (959830343 : ℚ) / 4149757785600

def SurrogateDiagonalTailChunk000Sub000Block021Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 923
    = surrogateDiagTailX0RatChunk000Sub000Block021Part006

theorem surrogateDiagonalTailChunk000Sub000Block021Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part006] using hcert

def TailChunk000Sub000Block021Part007SupportExplicit : Finset ℕ :=
  ([926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part007 : ℚ :=
  (13371266375 : ℚ) / 10356239273688

def SurrogateDiagonalTailChunk000Sub000Block021Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 926
    = surrogateDiagTailX0RatChunk000Sub000Block021Part007

theorem surrogateDiagonalTailChunk000Sub000Block021Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part007] using hcert

def TailChunk000Sub000Block021Part008SupportExplicit : Finset ℕ :=
  ([929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part008 : ℚ :=
  (134742276125 : ℚ) / 927232761790464

def SurrogateDiagonalTailChunk000Sub000Block021Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 929
    = surrogateDiagTailX0RatChunk000Sub000Block021Part008

theorem surrogateDiagonalTailChunk000Sub000Block021Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part008] using hcert

def TailChunk000Sub000Block021Part009SupportExplicit : Finset ℕ :=
  ([930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part009 : ℚ :=
  (508597079 : ℚ) / 55307059200

def SurrogateDiagonalTailChunk000Sub000Block021Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 930
    = surrogateDiagTailX0RatChunk000Sub000Block021Part009

theorem surrogateDiagonalTailChunk000Sub000Block021Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part009] using hcert

def TailChunk000Sub000Block021Part010SupportExplicit : Finset ℕ :=
  ([933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part010 : ℚ :=
  (4097432621 : ℚ) / 7389645633600

def SurrogateDiagonalTailChunk000Sub000Block021Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 933
    = surrogateDiagTailX0RatChunk000Sub000Block021Part010

theorem surrogateDiagonalTailChunk000Sub000Block021Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part010] using hcert

def TailChunk000Sub000Block021Part011SupportExplicit : Finset ℕ :=
  ([934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part011 : ℚ :=
  (149636315125 : ℚ) / 117915399204168

def SurrogateDiagonalTailChunk000Sub000Block021Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 934
    = surrogateDiagTailX0RatChunk000Sub000Block021Part011

theorem surrogateDiagonalTailChunk000Sub000Block021Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part011] using hcert

def TailChunk000Sub000Block021Part012SupportExplicit : Finset ℕ :=
  ([935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part012 : ℚ :=
  (8637842101 : ℚ) / 16780571443200

def SurrogateDiagonalTailChunk000Sub000Block021Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 935
    = surrogateDiagTailX0RatChunk000Sub000Block021Part012

theorem surrogateDiagonalTailChunk000Sub000Block021Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part012] using hcert

def TailChunk000Sub000Block021Part013SupportExplicit : Finset ℕ :=
  ([937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part013 : ℚ :=
  (137072910125 : ℚ) / 959622137570304

def SurrogateDiagonalTailChunk000Sub000Block021Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 937
    = surrogateDiagTailX0RatChunk000Sub000Block021Part013

theorem surrogateDiagonalTailChunk000Sub000Block021Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part013] using hcert

def TailChunk000Sub000Block021Part014SupportExplicit : Finset ℕ :=
  ([938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part014 : ℚ :=
  (117576258025 : ℚ) / 61490440268928

def SurrogateDiagonalTailChunk000Sub000Block021Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 938
    = surrogateDiagTailX0RatChunk000Sub000Block021Part014

theorem surrogateDiagonalTailChunk000Sub000Block021Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part014] using hcert

def TailChunk000Sub000Block021Part015SupportExplicit : Finset ℕ :=
  ([939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part015 : ℚ :=
  (189263808325 : ℚ) / 379109980274688

def SurrogateDiagonalTailChunk000Sub000Block021Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 939
    = surrogateDiagTailX0RatChunk000Sub000Block021Part015

theorem surrogateDiagonalTailChunk000Sub000Block021Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part015] using hcert

def TailChunk000Sub000Block021Part016SupportExplicit : Finset ℕ :=
  ([941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part016 : ℚ :=
  (1105965769 : ℚ) / 7809051097920

def SurrogateDiagonalTailChunk000Sub000Block021Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 941
    = surrogateDiagTailX0RatChunk000Sub000Block021Part016

theorem surrogateDiagonalTailChunk000Sub000Block021Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part016] using hcert

def TailChunk000Sub000Block021Part017SupportExplicit : Finset ℕ :=
  ([942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part017 : ℚ :=
  (6219103225 : ℚ) / 1480898360448

def SurrogateDiagonalTailChunk000Sub000Block021Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 942
    = surrogateDiagTailX0RatChunk000Sub000Block021Part017

theorem surrogateDiagonalTailChunk000Sub000Block021Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part017] using hcert

def TailChunk000Sub000Block021Part018SupportExplicit : Finset ℕ :=
  ([943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part018 : ℚ :=
  (10418232373 : ℚ) / 59981529907200

def SurrogateDiagonalTailChunk000Sub000Block021Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 943
    = surrogateDiagTailX0RatChunk000Sub000Block021Part018

theorem surrogateDiagonalTailChunk000Sub000Block021Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part018] using hcert

def TailChunk000Sub000Block021Part019SupportExplicit : Finset ℕ :=
  ([946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part019 : ℚ :=
  (5005171831 : ℚ) / 3112318339200

def SurrogateDiagonalTailChunk000Sub000Block021Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 946
    = surrogateDiagTailX0RatChunk000Sub000Block021Part019

theorem surrogateDiagonalTailChunk000Sub000Block021Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part019] using hcert

def TailChunk000Sub000Block021Part020SupportExplicit : Finset ℕ :=
  ([947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part020 : ℚ :=
  (111989023875 : ℚ) / 667529018321176

def SurrogateDiagonalTailChunk000Sub000Block021Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 947
    = surrogateDiagTailX0RatChunk000Sub000Block021Part020

theorem surrogateDiagonalTailChunk000Sub000Block021Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part020] using hcert

def TailChunk000Sub000Block021Part021SupportExplicit : Finset ℕ :=
  ([949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part021 : ℚ :=
  (33752642275 : ℚ) / 154824369242112

def SurrogateDiagonalTailChunk000Sub000Block021Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 949
    = surrogateDiagTailX0RatChunk000Sub000Block021Part021

theorem surrogateDiagonalTailChunk000Sub000Block021Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part021] using hcert

def TailChunk000Sub000Block021Part022SupportExplicit : Finset ℕ :=
  ([951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part022 : ℚ :=
  (106427269475 : ℚ) / 199464299602944

def SurrogateDiagonalTailChunk000Sub000Block021Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 951
    = surrogateDiagTailX0RatChunk000Sub000Block021Part022

theorem surrogateDiagonalTailChunk000Sub000Block021Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part022] using hcert

def TailChunk000Sub000Block021Part023SupportExplicit : Finset ℕ :=
  ([953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part023 : ℚ :=
  (141794130125 : ℚ) / 1026939022255104

def SurrogateDiagonalTailChunk000Sub000Block021Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 953
    = surrogateDiagTailX0RatChunk000Sub000Block021Part023

theorem surrogateDiagonalTailChunk000Sub000Block021Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part023] using hcert

def TailChunk000Sub000Block021Part024SupportExplicit : Finset ℕ :=
  ([955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block021Part024 : ℚ :=
  (611123433 : ℚ) / 2224589895680

def SurrogateDiagonalTailChunk000Sub000Block021Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 955
    = surrogateDiagTailX0RatChunk000Sub000Block021Part024

theorem surrogateDiagonalTailChunk000Sub000Block021Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block021Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block021Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block021Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block021Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block021Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block021HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block021Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block021Part000
    + surrogateDiagTailX0RatChunk000Sub000Block021Part001
    + surrogateDiagTailX0RatChunk000Sub000Block021Part002
    + surrogateDiagTailX0RatChunk000Sub000Block021Part003
    + surrogateDiagTailX0RatChunk000Sub000Block021Part004
    + surrogateDiagTailX0RatChunk000Sub000Block021Part005
    + surrogateDiagTailX0RatChunk000Sub000Block021Part006
    + surrogateDiagTailX0RatChunk000Sub000Block021Part007
    + surrogateDiagTailX0RatChunk000Sub000Block021Part008
    + surrogateDiagTailX0RatChunk000Sub000Block021Part009

def surrogateDiagonalTailChunk000Sub000Block021MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block021Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block021Part010
    + surrogateDiagTailX0RatChunk000Sub000Block021Part011
    + surrogateDiagTailX0RatChunk000Sub000Block021Part012
    + surrogateDiagTailX0RatChunk000Sub000Block021Part013
    + surrogateDiagTailX0RatChunk000Sub000Block021Part014
    + surrogateDiagTailX0RatChunk000Sub000Block021Part015
    + surrogateDiagTailX0RatChunk000Sub000Block021Part016
    + surrogateDiagTailX0RatChunk000Sub000Block021Part017
    + surrogateDiagTailX0RatChunk000Sub000Block021Part018
    + surrogateDiagTailX0RatChunk000Sub000Block021Part019

def surrogateDiagonalTailChunk000Sub000Block021TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block021Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block021Part020
    + surrogateDiagTailX0RatChunk000Sub000Block021Part021
    + surrogateDiagTailX0RatChunk000Sub000Block021Part022
    + surrogateDiagTailX0RatChunk000Sub000Block021Part023
    + surrogateDiagTailX0RatChunk000Sub000Block021Part024

def surrogateDiagonalTailChunk000Sub000Block021Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block021HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block021MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block021TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block021 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block021Part000
    + surrogateDiagTailX0RatChunk000Sub000Block021Part001
    + surrogateDiagTailX0RatChunk000Sub000Block021Part002
    + surrogateDiagTailX0RatChunk000Sub000Block021Part003
    + surrogateDiagTailX0RatChunk000Sub000Block021Part004
    + surrogateDiagTailX0RatChunk000Sub000Block021Part005
    + surrogateDiagTailX0RatChunk000Sub000Block021Part006
    + surrogateDiagTailX0RatChunk000Sub000Block021Part007
    + surrogateDiagTailX0RatChunk000Sub000Block021Part008
    + surrogateDiagTailX0RatChunk000Sub000Block021Part009
    + surrogateDiagTailX0RatChunk000Sub000Block021Part010
    + surrogateDiagTailX0RatChunk000Sub000Block021Part011
    + surrogateDiagTailX0RatChunk000Sub000Block021Part012
    + surrogateDiagTailX0RatChunk000Sub000Block021Part013
    + surrogateDiagTailX0RatChunk000Sub000Block021Part014
    + surrogateDiagTailX0RatChunk000Sub000Block021Part015
    + surrogateDiagTailX0RatChunk000Sub000Block021Part016
    + surrogateDiagTailX0RatChunk000Sub000Block021Part017
    + surrogateDiagTailX0RatChunk000Sub000Block021Part018
    + surrogateDiagTailX0RatChunk000Sub000Block021Part019
    + surrogateDiagTailX0RatChunk000Sub000Block021Part020
    + surrogateDiagTailX0RatChunk000Sub000Block021Part021
    + surrogateDiagTailX0RatChunk000Sub000Block021Part022
    + surrogateDiagTailX0RatChunk000Sub000Block021Part023
    + surrogateDiagTailX0RatChunk000Sub000Block021Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block021_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block021Head + surrogateDiagTailX0RatChunk000Sub000Block021Mid + surrogateDiagTailX0RatChunk000Sub000Block021Tail =
      surrogateDiagTailX0RatChunk000Sub000Block021 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block021Head surrogateDiagTailX0RatChunk000Sub000Block021Mid surrogateDiagTailX0RatChunk000Sub000Block021Tail surrogateDiagTailX0RatChunk000Sub000Block021
  ring

def SurrogateDiagonalTailChunk000Sub000Block021HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block021HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block021Head

def SurrogateDiagonalTailChunk000Sub000Block021MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block021MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block021Mid

def SurrogateDiagonalTailChunk000Sub000Block021TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block021TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block021Tail

theorem surrogateDiagonalTailChunk000Sub000Block021_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block021HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block021MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block021TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block021Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block021 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block021HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block021MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block021TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block021Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block021_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

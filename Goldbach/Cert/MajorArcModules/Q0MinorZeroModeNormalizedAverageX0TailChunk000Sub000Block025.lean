import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [25,26). -/

/- Block 025 covers tail-support indices [625,650) and q from 1082 to 1119. -/

def TailChunk000Sub000Block025Part000SupportExplicit : Finset ℕ :=
  ([1082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part000 : ℚ :=
  (3804853 : ℚ) / 4921734150

def SurrogateDiagonalTailChunk000Sub000Block025Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1082
    = surrogateDiagTailX0RatChunk000Sub000Block025Part000

theorem surrogateDiagonalTailChunk000Sub000Block025Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part000] using hcert

def TailChunk000Sub000Block025Part001SupportExplicit : Finset ℕ :=
  ([1085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part001 : ℚ :=
  (9485337073 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block025Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1085
    = surrogateDiagTailX0RatChunk000Sub000Block025Part001

theorem surrogateDiagonalTailChunk000Sub000Block025Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part001] using hcert

def TailChunk000Sub000Block025Part002SupportExplicit : Finset ℕ :=
  ([1086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part002 : ℚ :=
  (94474781 : ℚ) / 33599038464

def SurrogateDiagonalTailChunk000Sub000Block025Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1086
    = surrogateDiagTailX0RatChunk000Sub000Block025Part002

theorem surrogateDiagonalTailChunk000Sub000Block025Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part002] using hcert

def TailChunk000Sub000Block025Part003SupportExplicit : Finset ℕ :=
  ([1087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part003 : ℚ :=
  (184472460125 : ℚ) / 1739066399751204

def SurrogateDiagonalTailChunk000Sub000Block025Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1087
    = surrogateDiagTailX0RatChunk000Sub000Block025Part003

theorem surrogateDiagonalTailChunk000Sub000Block025Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part003] using hcert

def TailChunk000Sub000Block025Part004SupportExplicit : Finset ℕ :=
  ([1090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part004 : ℚ :=
  (133215165625 : ℚ) / 87088707698688

def SurrogateDiagonalTailChunk000Sub000Block025Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1090
    = surrogateDiagTailX0RatChunk000Sub000Block025Part004

theorem surrogateDiagonalTailChunk000Sub000Block025Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part004] using hcert

def TailChunk000Sub000Block025Part005SupportExplicit : Finset ℕ :=
  ([1091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part005 : ℚ :=
  (5947834157 : ℚ) / 70593196316100

def SurrogateDiagonalTailChunk000Sub000Block025Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1091
    = surrogateDiagTailX0RatChunk000Sub000Block025Part005

theorem surrogateDiagonalTailChunk000Sub000Block025Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part005] using hcert

def TailChunk000Sub000Block025Part006SupportExplicit : Finset ℕ :=
  ([1093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part006 : ℚ :=
  (186514575125 : ℚ) / 1777818481717824

def SurrogateDiagonalTailChunk000Sub000Block025Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1093
    = surrogateDiagTailX0RatChunk000Sub000Block025Part006

theorem surrogateDiagonalTailChunk000Sub000Block025Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part006] using hcert

def TailChunk000Sub000Block025Part007SupportExplicit : Finset ℕ :=
  ([1094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part007 : ℚ :=
  (59841800 : ℚ) / 79140779991

def SurrogateDiagonalTailChunk000Sub000Block025Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1094
    = surrogateDiagTailX0RatChunk000Sub000Block025Part007

theorem surrogateDiagonalTailChunk000Sub000Block025Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part007] using hcert

def TailChunk000Sub000Block025Part008SupportExplicit : Finset ℕ :=
  ([1095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part008 : ℚ :=
  (5839204175 : ℚ) / 8601353846784

def SurrogateDiagonalTailChunk000Sub000Block025Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1095
    = surrogateDiagTailX0RatChunk000Sub000Block025Part008

theorem surrogateDiagonalTailChunk000Sub000Block025Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part008] using hcert

def TailChunk000Sub000Block025Part009SupportExplicit : Finset ℕ :=
  ([1097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part009 : ℚ :=
  (187882230125 : ℚ) / 1804010578289664

def SurrogateDiagonalTailChunk000Sub000Block025Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1097
    = surrogateDiagTailX0RatChunk000Sub000Block025Part009

theorem surrogateDiagonalTailChunk000Sub000Block025Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part009] using hcert

def TailChunk000Sub000Block025Part010SupportExplicit : Finset ℕ :=
  ([1099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part010 : ℚ :=
  (17598279625 : ℚ) / 106624681952256

def SurrogateDiagonalTailChunk000Sub000Block025Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1099
    = surrogateDiagTailX0RatChunk000Sub000Block025Part010

theorem surrogateDiagonalTailChunk000Sub000Block025Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part010] using hcert

def TailChunk000Sub000Block025Part011SupportExplicit : Finset ℕ :=
  ([1101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part011 : ℚ :=
  (109169462975 : ℚ) / 358955975559744

def SurrogateDiagonalTailChunk000Sub000Block025Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1101
    = surrogateDiagTailX0RatChunk000Sub000Block025Part011

theorem surrogateDiagonalTailChunk000Sub000Block025Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part011] using hcert

def TailChunk000Sub000Block025Part012SupportExplicit : Finset ℕ :=
  ([1102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part012 : ℚ :=
  (156331689775 : ℚ) / 161342582704128

def SurrogateDiagonalTailChunk000Sub000Block025Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1102
    = surrogateDiagTailX0RatChunk000Sub000Block025Part012

theorem surrogateDiagonalTailChunk000Sub000Block025Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part012] using hcert

def TailChunk000Sub000Block025Part013SupportExplicit : Finset ℕ :=
  ([1103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part013 : ℚ :=
  (7999204175 : ℚ) / 97044212541516

def SurrogateDiagonalTailChunk000Sub000Block025Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1103
    = surrogateDiagTailX0RatChunk000Sub000Block025Part013

theorem surrogateDiagonalTailChunk000Sub000Block025Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part013] using hcert

def TailChunk000Sub000Block025Part014SupportExplicit : Finset ℕ :=
  ([1105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part014 : ℚ :=
  (85734105875 : ℚ) / 289968274538496

def SurrogateDiagonalTailChunk000Sub000Block025Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1105
    = surrogateDiagTailX0RatChunk000Sub000Block025Part014

theorem surrogateDiagonalTailChunk000Sub000Block025Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part014] using hcert

def TailChunk000Sub000Block025Part015SupportExplicit : Finset ℕ :=
  ([1106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part015 : ℚ :=
  (8089690525 : ℚ) / 6664042622016

def SurrogateDiagonalTailChunk000Sub000Block025Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1106
    = surrogateDiagTailX0RatChunk000Sub000Block025Part015

theorem surrogateDiagonalTailChunk000Sub000Block025Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part015] using hcert

def TailChunk000Sub000Block025Part016SupportExplicit : Finset ℕ :=
  ([1109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part016 : ℚ :=
  (192015171125 : ℚ) / 1884325410844224

def SurrogateDiagonalTailChunk000Sub000Block025Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1109
    = surrogateDiagTailX0RatChunk000Sub000Block025Part016

theorem surrogateDiagonalTailChunk000Sub000Block025Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part016] using hcert

def TailChunk000Sub000Block025Part017SupportExplicit : Finset ℕ :=
  ([1110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part017 : ℚ :=
  (89930606275 : ℚ) / 17202707693568

def SurrogateDiagonalTailChunk000Sub000Block025Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1110
    = surrogateDiagTailX0RatChunk000Sub000Block025Part017

theorem surrogateDiagonalTailChunk000Sub000Block025Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part017] using hcert

def TailChunk000Sub000Block025Part018SupportExplicit : Finset ℕ :=
  ([1111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part018 : ℚ :=
  (1804171 : ℚ) / 16003200000

def SurrogateDiagonalTailChunk000Sub000Block025Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1111
    = surrogateDiagTailX0RatChunk000Sub000Block025Part018

theorem surrogateDiagonalTailChunk000Sub000Block025Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part018] using hcert

def TailChunk000Sub000Block025Part019SupportExplicit : Finset ℕ :=
  ([1113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part019 : ℚ :=
  (12202875 : ℚ) / 24376927744

def SurrogateDiagonalTailChunk000Sub000Block025Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1113
    = surrogateDiagTailX0RatChunk000Sub000Block025Part019

theorem surrogateDiagonalTailChunk000Sub000Block025Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part019] using hcert

def TailChunk000Sub000Block025Part020SupportExplicit : Finset ℕ :=
  ([1114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part020 : ℚ :=
  (907478325 : ℚ) / 1244585670694

def SurrogateDiagonalTailChunk000Sub000Block025Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1114
    = surrogateDiagTailX0RatChunk000Sub000Block025Part020

theorem surrogateDiagonalTailChunk000Sub000Block025Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part020] using hcert

def TailChunk000Sub000Block025Part021SupportExplicit : Finset ℕ :=
  ([1115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part021 : ℚ :=
  (84624869675 : ℚ) / 518271666886656

def SurrogateDiagonalTailChunk000Sub000Block025Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1115
    = surrogateDiagTailX0RatChunk000Sub000Block025Part021

theorem surrogateDiagonalTailChunk000Sub000Block025Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part021] using hcert

def TailChunk000Sub000Block025Part022SupportExplicit : Finset ℕ :=
  ([1117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part022 : ℚ :=
  (194795445125 : ℚ) / 1939338600081984

def SurrogateDiagonalTailChunk000Sub000Block025Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1117
    = surrogateDiagTailX0RatChunk000Sub000Block025Part022

theorem surrogateDiagonalTailChunk000Sub000Block025Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part022] using hcert

def TailChunk000Sub000Block025Part023SupportExplicit : Finset ℕ :=
  ([1118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part023 : ℚ :=
  (79244220575 : ℚ) / 80671291352064

def SurrogateDiagonalTailChunk000Sub000Block025Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1118
    = surrogateDiagTailX0RatChunk000Sub000Block025Part023

theorem surrogateDiagonalTailChunk000Sub000Block025Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part023] using hcert

def TailChunk000Sub000Block025Part024SupportExplicit : Finset ℕ :=
  ([1119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block025Part024 : ℚ :=
  (242836977625 : ℚ) / 766158459291648

def SurrogateDiagonalTailChunk000Sub000Block025Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1119
    = surrogateDiagTailX0RatChunk000Sub000Block025Part024

theorem surrogateDiagonalTailChunk000Sub000Block025Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block025Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block025Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block025Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block025Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block025Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block025HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block025Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block025Part000
    + surrogateDiagTailX0RatChunk000Sub000Block025Part001
    + surrogateDiagTailX0RatChunk000Sub000Block025Part002
    + surrogateDiagTailX0RatChunk000Sub000Block025Part003
    + surrogateDiagTailX0RatChunk000Sub000Block025Part004
    + surrogateDiagTailX0RatChunk000Sub000Block025Part005
    + surrogateDiagTailX0RatChunk000Sub000Block025Part006
    + surrogateDiagTailX0RatChunk000Sub000Block025Part007
    + surrogateDiagTailX0RatChunk000Sub000Block025Part008
    + surrogateDiagTailX0RatChunk000Sub000Block025Part009

def surrogateDiagonalTailChunk000Sub000Block025MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block025Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block025Part010
    + surrogateDiagTailX0RatChunk000Sub000Block025Part011
    + surrogateDiagTailX0RatChunk000Sub000Block025Part012
    + surrogateDiagTailX0RatChunk000Sub000Block025Part013
    + surrogateDiagTailX0RatChunk000Sub000Block025Part014
    + surrogateDiagTailX0RatChunk000Sub000Block025Part015
    + surrogateDiagTailX0RatChunk000Sub000Block025Part016
    + surrogateDiagTailX0RatChunk000Sub000Block025Part017
    + surrogateDiagTailX0RatChunk000Sub000Block025Part018
    + surrogateDiagTailX0RatChunk000Sub000Block025Part019

def surrogateDiagonalTailChunk000Sub000Block025TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block025Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block025Part020
    + surrogateDiagTailX0RatChunk000Sub000Block025Part021
    + surrogateDiagTailX0RatChunk000Sub000Block025Part022
    + surrogateDiagTailX0RatChunk000Sub000Block025Part023
    + surrogateDiagTailX0RatChunk000Sub000Block025Part024

def surrogateDiagonalTailChunk000Sub000Block025Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block025HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block025MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block025TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block025 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block025Part000
    + surrogateDiagTailX0RatChunk000Sub000Block025Part001
    + surrogateDiagTailX0RatChunk000Sub000Block025Part002
    + surrogateDiagTailX0RatChunk000Sub000Block025Part003
    + surrogateDiagTailX0RatChunk000Sub000Block025Part004
    + surrogateDiagTailX0RatChunk000Sub000Block025Part005
    + surrogateDiagTailX0RatChunk000Sub000Block025Part006
    + surrogateDiagTailX0RatChunk000Sub000Block025Part007
    + surrogateDiagTailX0RatChunk000Sub000Block025Part008
    + surrogateDiagTailX0RatChunk000Sub000Block025Part009
    + surrogateDiagTailX0RatChunk000Sub000Block025Part010
    + surrogateDiagTailX0RatChunk000Sub000Block025Part011
    + surrogateDiagTailX0RatChunk000Sub000Block025Part012
    + surrogateDiagTailX0RatChunk000Sub000Block025Part013
    + surrogateDiagTailX0RatChunk000Sub000Block025Part014
    + surrogateDiagTailX0RatChunk000Sub000Block025Part015
    + surrogateDiagTailX0RatChunk000Sub000Block025Part016
    + surrogateDiagTailX0RatChunk000Sub000Block025Part017
    + surrogateDiagTailX0RatChunk000Sub000Block025Part018
    + surrogateDiagTailX0RatChunk000Sub000Block025Part019
    + surrogateDiagTailX0RatChunk000Sub000Block025Part020
    + surrogateDiagTailX0RatChunk000Sub000Block025Part021
    + surrogateDiagTailX0RatChunk000Sub000Block025Part022
    + surrogateDiagTailX0RatChunk000Sub000Block025Part023
    + surrogateDiagTailX0RatChunk000Sub000Block025Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block025_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block025Head + surrogateDiagTailX0RatChunk000Sub000Block025Mid + surrogateDiagTailX0RatChunk000Sub000Block025Tail =
      surrogateDiagTailX0RatChunk000Sub000Block025 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block025Head surrogateDiagTailX0RatChunk000Sub000Block025Mid surrogateDiagTailX0RatChunk000Sub000Block025Tail surrogateDiagTailX0RatChunk000Sub000Block025
  ring

def SurrogateDiagonalTailChunk000Sub000Block025HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block025HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block025Head

def SurrogateDiagonalTailChunk000Sub000Block025MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block025MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block025Mid

def SurrogateDiagonalTailChunk000Sub000Block025TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block025TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block025Tail

theorem surrogateDiagonalTailChunk000Sub000Block025_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block025HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block025MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block025TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block025Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block025 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block025HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block025MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block025TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block025Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block025_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

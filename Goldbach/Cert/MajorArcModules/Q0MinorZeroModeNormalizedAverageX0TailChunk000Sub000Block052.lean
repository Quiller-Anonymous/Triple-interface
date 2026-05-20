import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [52,53). -/

/- Block 052 covers tail-support indices [1300,1325) and q from 2191 to 2231. -/

def TailChunk000Sub000Block052Part000SupportExplicit : Finset ℕ :=
  ([2191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part000 : ℚ :=
  (131298307375 : ℚ) / 7676977100562432

def SurrogateDiagonalTailChunk000Sub000Block052Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2191
    = surrogateDiagTailX0RatChunk000Sub000Block052Part000

theorem surrogateDiagonalTailChunk000Sub000Block052Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part000] using hcert

def TailChunk000Sub000Block052Part001SupportExplicit : Finset ℕ :=
  ([2193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part001 : ℚ :=
  (60676950125 : ℚ) / 1019844473389056

def SurrogateDiagonalTailChunk000Sub000Block052Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2193
    = surrogateDiagTailX0RatChunk000Sub000Block052Part001

theorem surrogateDiagonalTailChunk000Sub000Block052Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part001] using hcert

def TailChunk000Sub000Block052Part002SupportExplicit : Finset ℕ :=
  ([2194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part002 : ℚ :=
  (187882230125 : ℚ) / 1804010578289664

def SurrogateDiagonalTailChunk000Sub000Block052Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2194
    = surrogateDiagTailX0RatChunk000Sub000Block052Part002

theorem surrogateDiagonalTailChunk000Sub000Block052Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part002] using hcert

def TailChunk000Sub000Block052Part003SupportExplicit : Finset ℕ :=
  ([2195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part003 : ℚ :=
  (684807076225 : ℚ) / 23559347942443008

def SurrogateDiagonalTailChunk000Sub000Block052Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2195
    = surrogateDiagTailX0RatChunk000Sub000Block052Part003

theorem surrogateDiagonalTailChunk000Sub000Block052Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part003] using hcert

def TailChunk000Sub000Block052Part004SupportExplicit : Finset ℕ :=
  ([2198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part004 : ℚ :=
  (17598279625 : ℚ) / 106624681952256

def SurrogateDiagonalTailChunk000Sub000Block052Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2198
    = surrogateDiagTailX0RatChunk000Sub000Block052Part004

theorem surrogateDiagonalTailChunk000Sub000Block052Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part004] using hcert

def TailChunk000Sub000Block052Part005SupportExplicit : Finset ℕ :=
  ([2199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part005 : ℚ :=
  (2981425 : ℚ) / 85068847104

def SurrogateDiagonalTailChunk000Sub000Block052Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2199
    = surrogateDiagTailX0RatChunk000Sub000Block052Part005

theorem surrogateDiagonalTailChunk000Sub000Block052Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part005] using hcert

def TailChunk000Sub000Block052Part006SupportExplicit : Finset ℕ :=
  ([2201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part006 : ℚ :=
  (3876195809 : ℚ) / 324199827000000

def SurrogateDiagonalTailChunk000Sub000Block052Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2201
    = surrogateDiagTailX0RatChunk000Sub000Block052Part006

theorem surrogateDiagonalTailChunk000Sub000Block052Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part006] using hcert

def TailChunk000Sub000Block052Part007SupportExplicit : Finset ℕ :=
  ([2202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part007 : ℚ :=
  (109169462975 : ℚ) / 358955975559744

def SurrogateDiagonalTailChunk000Sub000Block052Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2202
    = surrogateDiagTailX0RatChunk000Sub000Block052Part007

theorem surrogateDiagonalTailChunk000Sub000Block052Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part007] using hcert

def TailChunk000Sub000Block052Part008SupportExplicit : Finset ℕ :=
  ([2203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part008 : ℚ :=
  (101068077425 : ℚ) / 6532111780683912

def SurrogateDiagonalTailChunk000Sub000Block052Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2203
    = surrogateDiagTailX0RatChunk000Sub000Block052Part008

theorem surrogateDiagonalTailChunk000Sub000Block052Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part008] using hcert

def TailChunk000Sub000Block052Part009SupportExplicit : Finset ℕ :=
  ([2206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part009 : ℚ :=
  (7999204175 : ℚ) / 97044212541516

def SurrogateDiagonalTailChunk000Sub000Block052Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2206
    = surrogateDiagTailX0RatChunk000Sub000Block052Part009

theorem surrogateDiagonalTailChunk000Sub000Block052Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part009] using hcert

def TailChunk000Sub000Block052Part010SupportExplicit : Finset ℕ :=
  ([2207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part010 : ℚ :=
  (608734353775 : ℚ) / 59217339454911048

def SurrogateDiagonalTailChunk000Sub000Block052Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2207
    = surrogateDiagTailX0RatChunk000Sub000Block052Part010

theorem surrogateDiagonalTailChunk000Sub000Block052Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part010] using hcert

def TailChunk000Sub000Block052Part011SupportExplicit : Finset ℕ :=
  ([2210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part011 : ℚ :=
  (85734105875 : ℚ) / 289968274538496

def SurrogateDiagonalTailChunk000Sub000Block052Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2210
    = surrogateDiagTailX0RatChunk000Sub000Block052Part011

theorem surrogateDiagonalTailChunk000Sub000Block052Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part011] using hcert

def TailChunk000Sub000Block052Part012SupportExplicit : Finset ℕ :=
  ([2211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part012 : ℚ :=
  (15898714411 : ℚ) / 303656495155200

def SurrogateDiagonalTailChunk000Sub000Block052Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2211
    = surrogateDiagTailX0RatChunk000Sub000Block052Part012

theorem surrogateDiagonalTailChunk000Sub000Block052Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part012] using hcert

def TailChunk000Sub000Block052Part013SupportExplicit : Finset ℕ :=
  ([2213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part013 : ℚ :=
  (6244145475 : ℚ) / 407239611689344

def SurrogateDiagonalTailChunk000Sub000Block052Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2213
    = surrogateDiagTailX0RatChunk000Sub000Block052Part013

theorem surrogateDiagonalTailChunk000Sub000Block052Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part013] using hcert

def TailChunk000Sub000Block052Part014SupportExplicit : Finset ℕ :=
  ([2215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part014 : ℚ :=
  (167322187875 : ℚ) / 8143941528426496

def SurrogateDiagonalTailChunk000Sub000Block052Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2215
    = surrogateDiagTailX0RatChunk000Sub000Block052Part014

theorem surrogateDiagonalTailChunk000Sub000Block052Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part014] using hcert

def TailChunk000Sub000Block052Part015SupportExplicit : Finset ℕ :=
  ([2217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part015 : ℚ :=
  (110807341375 : ℚ) / 2966964141533472

def SurrogateDiagonalTailChunk000Sub000Block052Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2217
    = surrogateDiagTailX0RatChunk000Sub000Block052Part015

theorem surrogateDiagonalTailChunk000Sub000Block052Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part015] using hcert

def TailChunk000Sub000Block052Part016SupportExplicit : Finset ℕ :=
  ([2218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part016 : ℚ :=
  (192015171125 : ℚ) / 1884325410844224

def SurrogateDiagonalTailChunk000Sub000Block052Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2218
    = surrogateDiagTailX0RatChunk000Sub000Block052Part016

theorem surrogateDiagonalTailChunk000Sub000Block052Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part016] using hcert

def TailChunk000Sub000Block052Part017SupportExplicit : Finset ℕ :=
  ([2219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part017 : ℚ :=
  (134674451125 : ℚ) / 8078304133919232

def SurrogateDiagonalTailChunk000Sub000Block052Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2219
    = surrogateDiagTailX0RatChunk000Sub000Block052Part017

theorem surrogateDiagonalTailChunk000Sub000Block052Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part017] using hcert

def TailChunk000Sub000Block052Part018SupportExplicit : Finset ℕ :=
  ([2221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part018 : ℚ :=
  (24659272159 : ℚ) / 2429398438531200

def SurrogateDiagonalTailChunk000Sub000Block052Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2221
    = surrogateDiagTailX0RatChunk000Sub000Block052Part018

theorem surrogateDiagonalTailChunk000Sub000Block052Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part018] using hcert

def TailChunk000Sub000Block052Part019SupportExplicit : Finset ℕ :=
  ([2222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part019 : ℚ :=
  (1804171 : ℚ) / 16003200000

def SurrogateDiagonalTailChunk000Sub000Block052Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2222
    = surrogateDiagTailX0RatChunk000Sub000Block052Part019

theorem surrogateDiagonalTailChunk000Sub000Block052Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part019] using hcert

def TailChunk000Sub000Block052Part020SupportExplicit : Finset ℕ :=
  ([2226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part020 : ℚ :=
  (12202875 : ℚ) / 24376927744

def SurrogateDiagonalTailChunk000Sub000Block052Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2226
    = surrogateDiagTailX0RatChunk000Sub000Block052Part020

theorem surrogateDiagonalTailChunk000Sub000Block052Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part020] using hcert

def TailChunk000Sub000Block052Part021SupportExplicit : Finset ℕ :=
  ([2227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part021 : ℚ :=
  (23356092091 : ℚ) / 1872148050739200

def SurrogateDiagonalTailChunk000Sub000Block052Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2227
    = surrogateDiagTailX0RatChunk000Sub000Block052Part021

theorem surrogateDiagonalTailChunk000Sub000Block052Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part021] using hcert

def TailChunk000Sub000Block052Part022SupportExplicit : Finset ℕ :=
  ([2229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part022 : ℚ :=
  (56005031675 : ℚ) / 1515906711198096

def SurrogateDiagonalTailChunk000Sub000Block052Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2229
    = surrogateDiagTailX0RatChunk000Sub000Block052Part022

theorem surrogateDiagonalTailChunk000Sub000Block052Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part022] using hcert

def TailChunk000Sub000Block052Part023SupportExplicit : Finset ℕ :=
  ([2230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part023 : ℚ :=
  (84624869675 : ℚ) / 518271666886656

def SurrogateDiagonalTailChunk000Sub000Block052Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2230
    = surrogateDiagTailX0RatChunk000Sub000Block052Part023

theorem surrogateDiagonalTailChunk000Sub000Block052Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part023] using hcert

def TailChunk000Sub000Block052Part024SupportExplicit : Finset ℕ :=
  ([2231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block052Part024 : ℚ :=
  (593282168725 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block052Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2231
    = surrogateDiagTailX0RatChunk000Sub000Block052Part024

theorem surrogateDiagonalTailChunk000Sub000Block052Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block052Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block052Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block052Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block052Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block052Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block052HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block052Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block052Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block052Part000
    + surrogateDiagTailX0RatChunk000Sub000Block052Part001
    + surrogateDiagTailX0RatChunk000Sub000Block052Part002
    + surrogateDiagTailX0RatChunk000Sub000Block052Part003
    + surrogateDiagTailX0RatChunk000Sub000Block052Part004
    + surrogateDiagTailX0RatChunk000Sub000Block052Part005
    + surrogateDiagTailX0RatChunk000Sub000Block052Part006
    + surrogateDiagTailX0RatChunk000Sub000Block052Part007
    + surrogateDiagTailX0RatChunk000Sub000Block052Part008
    + surrogateDiagTailX0RatChunk000Sub000Block052Part009

def surrogateDiagonalTailChunk000Sub000Block052MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block052Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block052Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block052Part010
    + surrogateDiagTailX0RatChunk000Sub000Block052Part011
    + surrogateDiagTailX0RatChunk000Sub000Block052Part012
    + surrogateDiagTailX0RatChunk000Sub000Block052Part013
    + surrogateDiagTailX0RatChunk000Sub000Block052Part014
    + surrogateDiagTailX0RatChunk000Sub000Block052Part015
    + surrogateDiagTailX0RatChunk000Sub000Block052Part016
    + surrogateDiagTailX0RatChunk000Sub000Block052Part017
    + surrogateDiagTailX0RatChunk000Sub000Block052Part018
    + surrogateDiagTailX0RatChunk000Sub000Block052Part019

def surrogateDiagonalTailChunk000Sub000Block052TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block052Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block052Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block052Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block052Part020
    + surrogateDiagTailX0RatChunk000Sub000Block052Part021
    + surrogateDiagTailX0RatChunk000Sub000Block052Part022
    + surrogateDiagTailX0RatChunk000Sub000Block052Part023
    + surrogateDiagTailX0RatChunk000Sub000Block052Part024

def surrogateDiagonalTailChunk000Sub000Block052Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block052HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block052MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block052TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block052 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block052Part000
    + surrogateDiagTailX0RatChunk000Sub000Block052Part001
    + surrogateDiagTailX0RatChunk000Sub000Block052Part002
    + surrogateDiagTailX0RatChunk000Sub000Block052Part003
    + surrogateDiagTailX0RatChunk000Sub000Block052Part004
    + surrogateDiagTailX0RatChunk000Sub000Block052Part005
    + surrogateDiagTailX0RatChunk000Sub000Block052Part006
    + surrogateDiagTailX0RatChunk000Sub000Block052Part007
    + surrogateDiagTailX0RatChunk000Sub000Block052Part008
    + surrogateDiagTailX0RatChunk000Sub000Block052Part009
    + surrogateDiagTailX0RatChunk000Sub000Block052Part010
    + surrogateDiagTailX0RatChunk000Sub000Block052Part011
    + surrogateDiagTailX0RatChunk000Sub000Block052Part012
    + surrogateDiagTailX0RatChunk000Sub000Block052Part013
    + surrogateDiagTailX0RatChunk000Sub000Block052Part014
    + surrogateDiagTailX0RatChunk000Sub000Block052Part015
    + surrogateDiagTailX0RatChunk000Sub000Block052Part016
    + surrogateDiagTailX0RatChunk000Sub000Block052Part017
    + surrogateDiagTailX0RatChunk000Sub000Block052Part018
    + surrogateDiagTailX0RatChunk000Sub000Block052Part019
    + surrogateDiagTailX0RatChunk000Sub000Block052Part020
    + surrogateDiagTailX0RatChunk000Sub000Block052Part021
    + surrogateDiagTailX0RatChunk000Sub000Block052Part022
    + surrogateDiagTailX0RatChunk000Sub000Block052Part023
    + surrogateDiagTailX0RatChunk000Sub000Block052Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block052_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block052Head + surrogateDiagTailX0RatChunk000Sub000Block052Mid + surrogateDiagTailX0RatChunk000Sub000Block052Tail =
      surrogateDiagTailX0RatChunk000Sub000Block052 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block052Head surrogateDiagTailX0RatChunk000Sub000Block052Mid surrogateDiagTailX0RatChunk000Sub000Block052Tail surrogateDiagTailX0RatChunk000Sub000Block052
  ring

def SurrogateDiagonalTailChunk000Sub000Block052HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block052HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block052Head

def SurrogateDiagonalTailChunk000Sub000Block052MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block052MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block052Mid

def SurrogateDiagonalTailChunk000Sub000Block052TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block052TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block052Tail

theorem surrogateDiagonalTailChunk000Sub000Block052_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block052HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block052MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block052TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block052Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block052 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block052HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block052MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block052TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block052Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block052_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

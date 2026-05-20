import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [124,125). -/

/- Block 124 covers tail-support indices [3100,3125) and q from 5153 to 5189. -/

def TailChunk000Sub000Block124Part000SupportExplicit : Finset ℕ :=
  ([5153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part000 : ℚ :=
  (414897015625 : ℚ) / 440423298268004352

def SurrogateDiagonalTailChunk000Sub000Block124Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5153
    = surrogateDiagTailX0RatChunk000Sub000Block124Part000

theorem surrogateDiagonalTailChunk000Sub000Block124Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part000] using hcert

def TailChunk000Sub000Block124Part001SupportExplicit : Finset ℕ :=
  ([5154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part001 : ℚ :=
  (368743472275 : ℚ) / 21681832895319168

def SurrogateDiagonalTailChunk000Sub000Block124Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5154
    = surrogateDiagTailX0RatChunk000Sub000Block124Part001

theorem surrogateDiagonalTailChunk000Sub000Block124Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part001] using hcert

def TailChunk000Sub000Block124Part002SupportExplicit : Finset ℕ :=
  ([5155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part002 : ℚ :=
  (5310560899 : ℚ) / 2881878814110720

def SurrogateDiagonalTailChunk000Sub000Block124Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5155
    = surrogateDiagTailX0RatChunk000Sub000Block124Part002

theorem surrogateDiagonalTailChunk000Sub000Block124Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part002] using hcert

def TailChunk000Sub000Block124Part003SupportExplicit : Finset ℕ :=
  ([5158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part003 : ℚ :=
  (831238843975 : ℚ) / 110448166553907528

def SurrogateDiagonalTailChunk000Sub000Block124Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5158
    = surrogateDiagTailX0RatChunk000Sub000Block124Part003

theorem surrogateDiagonalTailChunk000Sub000Block124Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part003] using hcert

def TailChunk000Sub000Block124Part004SupportExplicit : Finset ℕ :=
  ([5159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part004 : ℚ :=
  (50658139501 : ℚ) / 24596176107571200

def SurrogateDiagonalTailChunk000Sub000Block124Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5159
    = surrogateDiagTailX0RatChunk000Sub000Block124Part004

theorem surrogateDiagonalTailChunk000Sub000Block124Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part004] using hcert

def TailChunk000Sub000Block124Part005SupportExplicit : Finset ℕ :=
  ([5161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part005 : ℚ :=
  (766503144875 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub000Block124Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5161
    = surrogateDiagTailX0RatChunk000Sub000Block124Part005

theorem surrogateDiagonalTailChunk000Sub000Block124Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part005] using hcert

def TailChunk000Sub000Block124Part006SupportExplicit : Finset ℕ :=
  ([5162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part006 : ℚ :=
  (264773025675 : ℚ) / 30723339372199936

def SurrogateDiagonalTailChunk000Sub000Block124Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5162
    = surrogateDiagTailX0RatChunk000Sub000Block124Part006

theorem surrogateDiagonalTailChunk000Sub000Block124Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part006] using hcert

def TailChunk000Sub000Block124Part007SupportExplicit : Finset ℕ :=
  ([5163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part007 : ℚ :=
  (4440099 : ℚ) / 1400340889600

def SurrogateDiagonalTailChunk000Sub000Block124Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5163
    = surrogateDiagTailX0RatChunk000Sub000Block124Part007

theorem surrogateDiagonalTailChunk000Sub000Block124Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part007] using hcert

def TailChunk000Sub000Block124Part008SupportExplicit : Finset ℕ :=
  ([5165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part008 : ℚ :=
  (211034295025 : ℚ) / 121013650752012288

def SurrogateDiagonalTailChunk000Sub000Block124Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5165
    = surrogateDiagTailX0RatChunk000Sub000Block124Part008

theorem surrogateDiagonalTailChunk000Sub000Block124Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part008] using hcert

def TailChunk000Sub000Block124Part009SupportExplicit : Finset ℕ :=
  ([5167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part009 : ℚ :=
  (417154515625 : ℚ) / 445230056488866642

def SurrogateDiagonalTailChunk000Sub000Block124Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5167
    = surrogateDiagTailX0RatChunk000Sub000Block124Part009

theorem surrogateDiagonalTailChunk000Sub000Block124Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part009] using hcert

def TailChunk000Sub000Block124Part010SupportExplicit : Finset ℕ :=
  ([5169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part010 : ℚ :=
  (108125 : ℚ) / 34180405056

def SurrogateDiagonalTailChunk000Sub000Block124Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5169
    = surrogateDiagTailX0RatChunk000Sub000Block124Part010

theorem surrogateDiagonalTailChunk000Sub000Block124Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part010] using hcert

def TailChunk000Sub000Block124Part011SupportExplicit : Finset ℕ :=
  ([5170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part011 : ℚ :=
  (23146032001 : ℚ) / 1146457981747200

def SurrogateDiagonalTailChunk000Sub000Block124Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5170
    = surrogateDiagTailX0RatChunk000Sub000Block124Part011

theorem surrogateDiagonalTailChunk000Sub000Block124Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part011] using hcert

def TailChunk000Sub000Block124Part012SupportExplicit : Finset ℕ :=
  ([5171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part012 : ℚ :=
  (668481025 : ℚ) / 714576982029042

def SurrogateDiagonalTailChunk000Sub000Block124Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5171
    = surrogateDiagTailX0RatChunk000Sub000Block124Part012

theorem surrogateDiagonalTailChunk000Sub000Block124Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part012] using hcert

def TailChunk000Sub000Block124Part013SupportExplicit : Finset ℕ :=
  ([5173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part013 : ℚ :=
  (26515715275 : ℚ) / 17801784849200832

def SurrogateDiagonalTailChunk000Sub000Block124Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5173
    = surrogateDiagTailX0RatChunk000Sub000Block124Part013

theorem surrogateDiagonalTailChunk000Sub000Block124Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part013] using hcert

def TailChunk000Sub000Block124Part014SupportExplicit : Finset ℕ :=
  ([5174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part014 : ℚ :=
  (42550804975 : ℚ) / 4427311699362816

def SurrogateDiagonalTailChunk000Sub000Block124Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5174
    = surrogateDiagTailX0RatChunk000Sub000Block124Part014

theorem surrogateDiagonalTailChunk000Sub000Block124Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part014] using hcert

def TailChunk000Sub000Block124Part015SupportExplicit : Finset ℕ :=
  ([5177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part015 : ℚ :=
  (32157375611 : ℚ) / 30759142606401600

def SurrogateDiagonalTailChunk000Sub000Block124Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5177
    = surrogateDiagTailX0RatChunk000Sub000Block124Part015

theorem surrogateDiagonalTailChunk000Sub000Block124Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part015] using hcert

def TailChunk000Sub000Block124Part016SupportExplicit : Finset ℕ :=
  ([5178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part016 : ℚ :=
  (111581475 : ℚ) / 4416915087488

def SurrogateDiagonalTailChunk000Sub000Block124Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5178
    = surrogateDiagTailX0RatChunk000Sub000Block124Part016

theorem surrogateDiagonalTailChunk000Sub000Block124Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part016] using hcert

def TailChunk000Sub000Block124Part017SupportExplicit : Finset ℕ :=
  ([5179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part017 : ℚ :=
  (419094390625 : ℚ) / 449381357622274482

def SurrogateDiagonalTailChunk000Sub000Block124Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5179
    = surrogateDiagTailX0RatChunk000Sub000Block124Part017

theorem surrogateDiagonalTailChunk000Sub000Block124Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part017] using hcert

def TailChunk000Sub000Block124Part018SupportExplicit : Finset ℕ :=
  ([5181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part018 : ℚ :=
  (6725074061 : ℚ) / 1579624917811200

def SurrogateDiagonalTailChunk000Sub000Block124Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5181
    = surrogateDiagTailX0RatChunk000Sub000Block124Part018

theorem surrogateDiagonalTailChunk000Sub000Block124Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part018] using hcert

def TailChunk000Sub000Block124Part019SupportExplicit : Finset ℕ :=
  ([5182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part019 : ℚ :=
  (33559691719 : ℚ) / 4500760533112200

def SurrogateDiagonalTailChunk000Sub000Block124Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5182
    = surrogateDiagTailX0RatChunk000Sub000Block124Part019

theorem surrogateDiagonalTailChunk000Sub000Block124Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part019] using hcert

def TailChunk000Sub000Block124Part020SupportExplicit : Finset ℕ :=
  ([5183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part020 : ℚ :=
  (8155343087 : ℚ) / 8067129135206400

def SurrogateDiagonalTailChunk000Sub000Block124Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5183
    = surrogateDiagTailX0RatChunk000Sub000Block124Part020

theorem surrogateDiagonalTailChunk000Sub000Block124Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part020] using hcert

def TailChunk000Sub000Block124Part021SupportExplicit : Finset ℕ :=
  ([5185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part021 : ℚ :=
  (15766845563 : ℚ) / 7249206863462400

def SurrogateDiagonalTailChunk000Sub000Block124Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5185
    = surrogateDiagTailX0RatChunk000Sub000Block124Part021

theorem surrogateDiagonalTailChunk000Sub000Block124Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part021] using hcert

def TailChunk000Sub000Block124Part022SupportExplicit : Finset ℕ :=
  ([5186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part022 : ℚ :=
  (840288033775 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block124Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5186
    = surrogateDiagTailX0RatChunk000Sub000Block124Part022

theorem surrogateDiagonalTailChunk000Sub000Block124Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part022] using hcert

def TailChunk000Sub000Block124Part023SupportExplicit : Finset ℕ :=
  ([5187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part023 : ℚ :=
  (831692489125 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block124Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5187
    = surrogateDiagTailX0RatChunk000Sub000Block124Part023

theorem surrogateDiagonalTailChunk000Sub000Block124Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part023] using hcert

def TailChunk000Sub000Block124Part024SupportExplicit : Finset ℕ :=
  ([5189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block124Part024 : ℚ :=
  (420714390625 : ℚ) / 452862893616789792

def SurrogateDiagonalTailChunk000Sub000Block124Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5189
    = surrogateDiagTailX0RatChunk000Sub000Block124Part024

theorem surrogateDiagonalTailChunk000Sub000Block124Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block124Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block124Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block124Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block124Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block124Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block124HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block124Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block124Part000
    + surrogateDiagTailX0RatChunk000Sub000Block124Part001
    + surrogateDiagTailX0RatChunk000Sub000Block124Part002
    + surrogateDiagTailX0RatChunk000Sub000Block124Part003
    + surrogateDiagTailX0RatChunk000Sub000Block124Part004
    + surrogateDiagTailX0RatChunk000Sub000Block124Part005
    + surrogateDiagTailX0RatChunk000Sub000Block124Part006
    + surrogateDiagTailX0RatChunk000Sub000Block124Part007
    + surrogateDiagTailX0RatChunk000Sub000Block124Part008
    + surrogateDiagTailX0RatChunk000Sub000Block124Part009

def surrogateDiagonalTailChunk000Sub000Block124MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block124Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block124Part010
    + surrogateDiagTailX0RatChunk000Sub000Block124Part011
    + surrogateDiagTailX0RatChunk000Sub000Block124Part012
    + surrogateDiagTailX0RatChunk000Sub000Block124Part013
    + surrogateDiagTailX0RatChunk000Sub000Block124Part014
    + surrogateDiagTailX0RatChunk000Sub000Block124Part015
    + surrogateDiagTailX0RatChunk000Sub000Block124Part016
    + surrogateDiagTailX0RatChunk000Sub000Block124Part017
    + surrogateDiagTailX0RatChunk000Sub000Block124Part018
    + surrogateDiagTailX0RatChunk000Sub000Block124Part019

def surrogateDiagonalTailChunk000Sub000Block124TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block124Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block124Part020
    + surrogateDiagTailX0RatChunk000Sub000Block124Part021
    + surrogateDiagTailX0RatChunk000Sub000Block124Part022
    + surrogateDiagTailX0RatChunk000Sub000Block124Part023
    + surrogateDiagTailX0RatChunk000Sub000Block124Part024

def surrogateDiagonalTailChunk000Sub000Block124Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block124HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block124MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block124TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block124 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block124Part000
    + surrogateDiagTailX0RatChunk000Sub000Block124Part001
    + surrogateDiagTailX0RatChunk000Sub000Block124Part002
    + surrogateDiagTailX0RatChunk000Sub000Block124Part003
    + surrogateDiagTailX0RatChunk000Sub000Block124Part004
    + surrogateDiagTailX0RatChunk000Sub000Block124Part005
    + surrogateDiagTailX0RatChunk000Sub000Block124Part006
    + surrogateDiagTailX0RatChunk000Sub000Block124Part007
    + surrogateDiagTailX0RatChunk000Sub000Block124Part008
    + surrogateDiagTailX0RatChunk000Sub000Block124Part009
    + surrogateDiagTailX0RatChunk000Sub000Block124Part010
    + surrogateDiagTailX0RatChunk000Sub000Block124Part011
    + surrogateDiagTailX0RatChunk000Sub000Block124Part012
    + surrogateDiagTailX0RatChunk000Sub000Block124Part013
    + surrogateDiagTailX0RatChunk000Sub000Block124Part014
    + surrogateDiagTailX0RatChunk000Sub000Block124Part015
    + surrogateDiagTailX0RatChunk000Sub000Block124Part016
    + surrogateDiagTailX0RatChunk000Sub000Block124Part017
    + surrogateDiagTailX0RatChunk000Sub000Block124Part018
    + surrogateDiagTailX0RatChunk000Sub000Block124Part019
    + surrogateDiagTailX0RatChunk000Sub000Block124Part020
    + surrogateDiagTailX0RatChunk000Sub000Block124Part021
    + surrogateDiagTailX0RatChunk000Sub000Block124Part022
    + surrogateDiagTailX0RatChunk000Sub000Block124Part023
    + surrogateDiagTailX0RatChunk000Sub000Block124Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block124_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block124Head + surrogateDiagTailX0RatChunk000Sub000Block124Mid + surrogateDiagTailX0RatChunk000Sub000Block124Tail =
      surrogateDiagTailX0RatChunk000Sub000Block124 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block124Head surrogateDiagTailX0RatChunk000Sub000Block124Mid surrogateDiagTailX0RatChunk000Sub000Block124Tail surrogateDiagTailX0RatChunk000Sub000Block124
  ring

def SurrogateDiagonalTailChunk000Sub000Block124HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block124HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block124Head

def SurrogateDiagonalTailChunk000Sub000Block124MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block124MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block124Mid

def SurrogateDiagonalTailChunk000Sub000Block124TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block124TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block124Tail

theorem surrogateDiagonalTailChunk000Sub000Block124_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block124HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block124MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block124TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block124Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block124 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block124HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block124MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block124TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block124Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block124_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [51,52). -/

/- Block 051 covers tail-support indices [1275,1300) and q from 2149 to 2190. -/

def TailChunk000Sub000Block051Part000SupportExplicit : Finset ℕ :=
  ([2149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part000 : ℚ :=
  (126314732125 : ℚ) / 7103257769240352

def SurrogateDiagonalTailChunk000Sub000Block051Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2149
    = surrogateDiagTailX0RatChunk000Sub000Block051Part000

theorem surrogateDiagonalTailChunk000Sub000Block051Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part000] using hcert

def TailChunk000Sub000Block051Part001SupportExplicit : Finset ℕ :=
  ([2153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part001 : ℚ :=
  (579310239775 : ℚ) / 53628534209169408

def SurrogateDiagonalTailChunk000Sub000Block051Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2153
    = surrogateDiagTailX0RatChunk000Sub000Block051Part001

theorem surrogateDiagonalTailChunk000Sub000Block051Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part001] using hcert

def TailChunk000Sub000Block051Part002SupportExplicit : Finset ℕ :=
  ([2154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part002 : ℚ :=
  (104462666975 : ℚ) / 328585921963584

def SurrogateDiagonalTailChunk000Sub000Block051Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2154
    = surrogateDiagTailX0RatChunk000Sub000Block051Part002

theorem surrogateDiagonalTailChunk000Sub000Block051Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part002] using hcert

def TailChunk000Sub000Block051Part003SupportExplicit : Finset ℕ :=
  ([2155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part003 : ℚ :=
  (253411911 : ℚ) / 11671841314816

def SurrogateDiagonalTailChunk000Sub000Block051Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2155
    = surrogateDiagTailX0RatChunk000Sub000Block051Part003

theorem surrogateDiagonalTailChunk000Sub000Block051Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part003] using hcert

def TailChunk000Sub000Block051Part004SupportExplicit : Finset ℕ :=
  ([2157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part004 : ℚ :=
  (516225506575 : ℚ) / 10632725902996608

def SurrogateDiagonalTailChunk000Sub000Block051Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2157
    = surrogateDiagTailX0RatChunk000Sub000Block051Part004

theorem surrogateDiagonalTailChunk000Sub000Block051Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part004] using hcert

def TailChunk000Sub000Block051Part005SupportExplicit : Finset ℕ :=
  ([2158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part005 : ℚ :=
  (54910430125 : ℚ) / 390711327280128

def SurrogateDiagonalTailChunk000Sub000Block051Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2158
    = surrogateDiagTailX0RatChunk000Sub000Block051Part005

theorem surrogateDiagonalTailChunk000Sub000Block051Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part005] using hcert

def TailChunk000Sub000Block051Part006SupportExplicit : Finset ℕ :=
  ([2159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part006 : ℚ :=
  (549814074025 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub000Block051Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2159
    = surrogateDiagTailX0RatChunk000Sub000Block051Part006

theorem surrogateDiagonalTailChunk000Sub000Block051Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part006] using hcert

def TailChunk000Sub000Block051Part007SupportExplicit : Finset ℕ :=
  ([2161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part007 : ℚ :=
  (23344935079 : ℚ) / 2177217692467200

def SurrogateDiagonalTailChunk000Sub000Block051Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2161
    = surrogateDiagTailX0RatChunk000Sub000Block051Part007

theorem surrogateDiagonalTailChunk000Sub000Block051Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part007] using hcert

def TailChunk000Sub000Block051Part008SupportExplicit : Finset ℕ :=
  ([2162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part008 : ℚ :=
  (340173615475 : ℚ) / 2622701767306368

def SurrogateDiagonalTailChunk000Sub000Block051Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2162
    = surrogateDiagTailX0RatChunk000Sub000Block051Part008

theorem surrogateDiagonalTailChunk000Sub000Block051Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part008] using hcert

def TailChunk000Sub000Block051Part009SupportExplicit : Finset ℕ :=
  ([2163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part009 : ℚ :=
  (362068089925 : ℚ) / 5612450583103488

def SurrogateDiagonalTailChunk000Sub000Block051Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2163
    = surrogateDiagTailX0RatChunk000Sub000Block051Part009

theorem surrogateDiagonalTailChunk000Sub000Block051Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part009] using hcert

def TailChunk000Sub000Block051Part010SupportExplicit : Finset ℕ :=
  ([2165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part010 : ℚ :=
  (666207693775 : ℚ) / 22294709170864128

def SurrogateDiagonalTailChunk000Sub000Block051Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2165
    = surrogateDiagTailX0RatChunk000Sub000Block051Part010

theorem surrogateDiagonalTailChunk000Sub000Block051Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part010] using hcert

def TailChunk000Sub000Block051Part011SupportExplicit : Finset ℕ :=
  ([2167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part011 : ℚ :=
  (2155641 : ℚ) / 102463155200

def SurrogateDiagonalTailChunk000Sub000Block051Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2167
    = surrogateDiagTailX0RatChunk000Sub000Block051Part011

theorem surrogateDiagonalTailChunk000Sub000Block051Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part011] using hcert

def TailChunk000Sub000Block051Part012SupportExplicit : Finset ℕ :=
  ([2170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part012 : ℚ :=
  (9485337073 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block051Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2170
    = surrogateDiagTailX0RatChunk000Sub000Block051Part012

theorem surrogateDiagonalTailChunk000Sub000Block051Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part012] using hcert

def TailChunk000Sub000Block051Part013SupportExplicit : Finset ℕ :=
  ([2171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part013 : ℚ :=
  (17073394475 : ℚ) / 1230365704256064

def SurrogateDiagonalTailChunk000Sub000Block051Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2171
    = surrogateDiagTailX0RatChunk000Sub000Block051Part013

theorem surrogateDiagonalTailChunk000Sub000Block051Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part013] using hcert

def TailChunk000Sub000Block051Part014SupportExplicit : Finset ℕ :=
  ([2173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part014 : ℚ :=
  (7585652493 : ℚ) / 624049350246400

def SurrogateDiagonalTailChunk000Sub000Block051Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2173
    = surrogateDiagTailX0RatChunk000Sub000Block051Part014

theorem surrogateDiagonalTailChunk000Sub000Block051Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part014] using hcert

def TailChunk000Sub000Block051Part015SupportExplicit : Finset ℕ :=
  ([2174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part015 : ℚ :=
  (184472460125 : ℚ) / 1739066399751204

def SurrogateDiagonalTailChunk000Sub000Block051Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2174
    = surrogateDiagTailX0RatChunk000Sub000Block051Part015

theorem surrogateDiagonalTailChunk000Sub000Block051Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part015] using hcert

def TailChunk000Sub000Block051Part016SupportExplicit : Finset ℕ :=
  ([2177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part016 : ℚ :=
  (5185054543 : ℚ) / 299280648160800

def SurrogateDiagonalTailChunk000Sub000Block051Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2177
    = surrogateDiagTailX0RatChunk000Sub000Block051Part016

theorem surrogateDiagonalTailChunk000Sub000Block051Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part016] using hcert

def TailChunk000Sub000Block051Part017SupportExplicit : Finset ℕ :=
  ([2179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part017 : ℚ :=
  (593386423975 : ℚ) / 56267595998585928

def SurrogateDiagonalTailChunk000Sub000Block051Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2179
    = surrogateDiagTailX0RatChunk000Sub000Block051Part017

theorem surrogateDiagonalTailChunk000Sub000Block051Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part017] using hcert

def TailChunk000Sub000Block051Part018SupportExplicit : Finset ℕ :=
  ([2181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part018 : ℚ :=
  (53619091325 : ℚ) / 1389323357989776

def SurrogateDiagonalTailChunk000Sub000Block051Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2181
    = surrogateDiagTailX0RatChunk000Sub000Block051Part018

theorem surrogateDiagonalTailChunk000Sub000Block051Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part018] using hcert

def TailChunk000Sub000Block051Part019SupportExplicit : Finset ℕ :=
  ([2182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part019 : ℚ :=
  (5947834157 : ℚ) / 70593196316100

def SurrogateDiagonalTailChunk000Sub000Block051Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2182
    = surrogateDiagTailX0RatChunk000Sub000Block051Part019

theorem surrogateDiagonalTailChunk000Sub000Block051Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part019] using hcert

def TailChunk000Sub000Block051Part020SupportExplicit : Finset ℕ :=
  ([2183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part020 : ℚ :=
  (573600217525 : ℚ) / 47527923047712768

def SurrogateDiagonalTailChunk000Sub000Block051Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2183
    = surrogateDiagTailX0RatChunk000Sub000Block051Part020

theorem surrogateDiagonalTailChunk000Sub000Block051Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part020] using hcert

def TailChunk000Sub000Block051Part021SupportExplicit : Finset ℕ :=
  ([2185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part021 : ℚ :=
  (49574468125 : ℚ) / 1311796059070464

def SurrogateDiagonalTailChunk000Sub000Block051Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2185
    = surrogateDiagTailX0RatChunk000Sub000Block051Part021

theorem surrogateDiagonalTailChunk000Sub000Block051Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part021] using hcert

def TailChunk000Sub000Block051Part022SupportExplicit : Finset ℕ :=
  ([2186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part022 : ℚ :=
  (186514575125 : ℚ) / 1777818481717824

def SurrogateDiagonalTailChunk000Sub000Block051Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2186
    = surrogateDiagTailX0RatChunk000Sub000Block051Part022

theorem surrogateDiagonalTailChunk000Sub000Block051Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part022] using hcert

def TailChunk000Sub000Block051Part023SupportExplicit : Finset ℕ :=
  ([2189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part023 : ℚ :=
  (21985003057 : ℚ) / 1537261006723200

def SurrogateDiagonalTailChunk000Sub000Block051Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2189
    = surrogateDiagTailX0RatChunk000Sub000Block051Part023

theorem surrogateDiagonalTailChunk000Sub000Block051Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part023] using hcert

def TailChunk000Sub000Block051Part024SupportExplicit : Finset ℕ :=
  ([2190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block051Part024 : ℚ :=
  (5839204175 : ℚ) / 8601353846784

def SurrogateDiagonalTailChunk000Sub000Block051Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2190
    = surrogateDiagTailX0RatChunk000Sub000Block051Part024

theorem surrogateDiagonalTailChunk000Sub000Block051Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block051Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block051Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block051Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block051Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block051Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block051HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block051Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block051Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block051Part000
    + surrogateDiagTailX0RatChunk000Sub000Block051Part001
    + surrogateDiagTailX0RatChunk000Sub000Block051Part002
    + surrogateDiagTailX0RatChunk000Sub000Block051Part003
    + surrogateDiagTailX0RatChunk000Sub000Block051Part004
    + surrogateDiagTailX0RatChunk000Sub000Block051Part005
    + surrogateDiagTailX0RatChunk000Sub000Block051Part006
    + surrogateDiagTailX0RatChunk000Sub000Block051Part007
    + surrogateDiagTailX0RatChunk000Sub000Block051Part008
    + surrogateDiagTailX0RatChunk000Sub000Block051Part009

def surrogateDiagonalTailChunk000Sub000Block051MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block051Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block051Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block051Part010
    + surrogateDiagTailX0RatChunk000Sub000Block051Part011
    + surrogateDiagTailX0RatChunk000Sub000Block051Part012
    + surrogateDiagTailX0RatChunk000Sub000Block051Part013
    + surrogateDiagTailX0RatChunk000Sub000Block051Part014
    + surrogateDiagTailX0RatChunk000Sub000Block051Part015
    + surrogateDiagTailX0RatChunk000Sub000Block051Part016
    + surrogateDiagTailX0RatChunk000Sub000Block051Part017
    + surrogateDiagTailX0RatChunk000Sub000Block051Part018
    + surrogateDiagTailX0RatChunk000Sub000Block051Part019

def surrogateDiagonalTailChunk000Sub000Block051TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block051Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block051Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block051Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block051Part020
    + surrogateDiagTailX0RatChunk000Sub000Block051Part021
    + surrogateDiagTailX0RatChunk000Sub000Block051Part022
    + surrogateDiagTailX0RatChunk000Sub000Block051Part023
    + surrogateDiagTailX0RatChunk000Sub000Block051Part024

def surrogateDiagonalTailChunk000Sub000Block051Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block051HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block051MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block051TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block051 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block051Part000
    + surrogateDiagTailX0RatChunk000Sub000Block051Part001
    + surrogateDiagTailX0RatChunk000Sub000Block051Part002
    + surrogateDiagTailX0RatChunk000Sub000Block051Part003
    + surrogateDiagTailX0RatChunk000Sub000Block051Part004
    + surrogateDiagTailX0RatChunk000Sub000Block051Part005
    + surrogateDiagTailX0RatChunk000Sub000Block051Part006
    + surrogateDiagTailX0RatChunk000Sub000Block051Part007
    + surrogateDiagTailX0RatChunk000Sub000Block051Part008
    + surrogateDiagTailX0RatChunk000Sub000Block051Part009
    + surrogateDiagTailX0RatChunk000Sub000Block051Part010
    + surrogateDiagTailX0RatChunk000Sub000Block051Part011
    + surrogateDiagTailX0RatChunk000Sub000Block051Part012
    + surrogateDiagTailX0RatChunk000Sub000Block051Part013
    + surrogateDiagTailX0RatChunk000Sub000Block051Part014
    + surrogateDiagTailX0RatChunk000Sub000Block051Part015
    + surrogateDiagTailX0RatChunk000Sub000Block051Part016
    + surrogateDiagTailX0RatChunk000Sub000Block051Part017
    + surrogateDiagTailX0RatChunk000Sub000Block051Part018
    + surrogateDiagTailX0RatChunk000Sub000Block051Part019
    + surrogateDiagTailX0RatChunk000Sub000Block051Part020
    + surrogateDiagTailX0RatChunk000Sub000Block051Part021
    + surrogateDiagTailX0RatChunk000Sub000Block051Part022
    + surrogateDiagTailX0RatChunk000Sub000Block051Part023
    + surrogateDiagTailX0RatChunk000Sub000Block051Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block051_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block051Head + surrogateDiagTailX0RatChunk000Sub000Block051Mid + surrogateDiagTailX0RatChunk000Sub000Block051Tail =
      surrogateDiagTailX0RatChunk000Sub000Block051 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block051Head surrogateDiagTailX0RatChunk000Sub000Block051Mid surrogateDiagTailX0RatChunk000Sub000Block051Tail surrogateDiagTailX0RatChunk000Sub000Block051
  ring

def SurrogateDiagonalTailChunk000Sub000Block051HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block051HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block051Head

def SurrogateDiagonalTailChunk000Sub000Block051MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block051MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block051Mid

def SurrogateDiagonalTailChunk000Sub000Block051TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block051TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block051Tail

theorem surrogateDiagonalTailChunk000Sub000Block051_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block051HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block051MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block051TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block051Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block051 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block051HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block051MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block051TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block051Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block051_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

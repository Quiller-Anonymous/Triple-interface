import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [41,42). -/

/- Block 041 covers tail-support indices [1025,1050) and q from 1738 to 1777. -/

def TailChunk000Sub000Block041Part000SupportExplicit : Finset ℕ :=
  ([1738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part000 : ℚ :=
  (2529609661 : ℚ) / 9255614752800

def SurrogateDiagonalTailChunk000Sub000Block041Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1738
    = surrogateDiagTailX0RatChunk000Sub000Block041Part000

theorem surrogateDiagonalTailChunk000Sub000Block041Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part000] using hcert

def TailChunk000Sub000Block041Part001SupportExplicit : Finset ℕ :=
  ([1739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part001 : ℚ :=
  (538906471375 : ℚ) / 18804777045608448

def SurrogateDiagonalTailChunk000Sub000Block041Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1739
    = surrogateDiagTailX0RatChunk000Sub000Block041Part001

theorem surrogateDiagonalTailChunk000Sub000Block041Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part001] using hcert

def TailChunk000Sub000Block041Part002SupportExplicit : Finset ℕ :=
  ([1741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part002 : ℚ :=
  (2524890473 : ℚ) / 101868833692800

def SurrogateDiagonalTailChunk000Sub000Block041Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1741
    = surrogateDiagTailX0RatChunk000Sub000Block041Part002

theorem surrogateDiagonalTailChunk000Sub000Block041Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part002] using hcert

def TailChunk000Sub000Block041Part003SupportExplicit : Finset ℕ :=
  ([1742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part003 : ℚ :=
  (218819702875 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block041Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1742
    = surrogateDiagTailX0RatChunk000Sub000Block041Part003

theorem surrogateDiagonalTailChunk000Sub000Block041Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part003] using hcert

def TailChunk000Sub000Block041Part004SupportExplicit : Finset ℕ :=
  ([1743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part004 : ℚ :=
  (5314825 : ℚ) / 39063320064

def SurrogateDiagonalTailChunk000Sub000Block041Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1743
    = surrogateDiagTailX0RatChunk000Sub000Block041Part004

theorem surrogateDiagonalTailChunk000Sub000Block041Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part004] using hcert

def TailChunk000Sub000Block041Part005SupportExplicit : Finset ℕ :=
  ([1745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part005 : ℚ :=
  (74651064725 : ℚ) / 1564705285521408

def SurrogateDiagonalTailChunk000Sub000Block041Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1745
    = surrogateDiagTailX0RatChunk000Sub000Block041Part005

theorem surrogateDiagonalTailChunk000Sub000Block041Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part005] using hcert

def TailChunk000Sub000Block041Part006SupportExplicit : Finset ℕ :=
  ([1747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part006 : ℚ :=
  (63558087425 : ℚ) / 2582030136726792

def SurrogateDiagonalTailChunk000Sub000Block041Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1747
    = surrogateDiagTailX0RatChunk000Sub000Block041Part006

theorem surrogateDiagonalTailChunk000Sub000Block041Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part006] using hcert

def TailChunk000Sub000Block041Part007SupportExplicit : Finset ℕ :=
  ([1749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part007 : ℚ :=
  (1045056889 : ℚ) / 9000711782400

def SurrogateDiagonalTailChunk000Sub000Block041Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1749
    = surrogateDiagTailX0RatChunk000Sub000Block041Part007

theorem surrogateDiagonalTailChunk000Sub000Block041Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part007] using hcert

def TailChunk000Sub000Block041Part008SupportExplicit : Finset ℕ :=
  ([1751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part008 : ℚ :=
  (59300680925 : ℚ) / 1970901713682432

def SurrogateDiagonalTailChunk000Sub000Block041Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1751
    = surrogateDiagTailX0RatChunk000Sub000Block041Part008

theorem surrogateDiagonalTailChunk000Sub000Block041Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part008] using hcert

def TailChunk000Sub000Block041Part009SupportExplicit : Finset ℕ :=
  ([1753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part009 : ℚ :=
  (63995412425 : ℚ) / 2617705326938112

def SurrogateDiagonalTailChunk000Sub000Block041Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1753
    = surrogateDiagTailX0RatChunk000Sub000Block041Part009

theorem surrogateDiagonalTailChunk000Sub000Block041Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part009] using hcert

def TailChunk000Sub000Block041Part010SupportExplicit : Finset ℕ :=
  ([1754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part010 : ℚ :=
  (120080265125 : ℚ) / 736229623201344

def SurrogateDiagonalTailChunk000Sub000Block041Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1754
    = surrogateDiagTailX0RatChunk000Sub000Block041Part010

theorem surrogateDiagonalTailChunk000Sub000Block041Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part010] using hcert

def TailChunk000Sub000Block041Part011SupportExplicit : Finset ℕ :=
  ([1757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part011 : ℚ :=
  (19453429921 : ℚ) / 506351250000000

def SurrogateDiagonalTailChunk000Sub000Block041Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1757
    = surrogateDiagTailX0RatChunk000Sub000Block041Part011

theorem surrogateDiagonalTailChunk000Sub000Block041Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part011] using hcert

def TailChunk000Sub000Block041Part012SupportExplicit : Finset ℕ :=
  ([1758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part012 : ℚ :=
  (187174291975 : ℚ) / 290856147437568

def SurrogateDiagonalTailChunk000Sub000Block041Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1758
    = surrogateDiagTailX0RatChunk000Sub000Block041Part012

theorem surrogateDiagonalTailChunk000Sub000Block041Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part012] using hcert

def TailChunk000Sub000Block041Part013SupportExplicit : Finset ℕ :=
  ([1759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part013 : ℚ :=
  (64434236825 : ℚ) / 2653748932017672

def SurrogateDiagonalTailChunk000Sub000Block041Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1759
    = surrogateDiagTailX0RatChunk000Sub000Block041Part013

theorem surrogateDiagonalTailChunk000Sub000Block041Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part013] using hcert

def TailChunk000Sub000Block041Part014SupportExplicit : Finset ℕ :=
  ([1761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part014 : ℚ :=
  (19347225 : ℚ) / 235841625632

def SurrogateDiagonalTailChunk000Sub000Block041Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1761
    = surrogateDiagTailX0RatChunk000Sub000Block041Part014

theorem surrogateDiagonalTailChunk000Sub000Block041Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part014] using hcert

def TailChunk000Sub000Block041Part015SupportExplicit : Finset ℕ :=
  ([1762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part015 : ℚ :=
  (775384839 : ℚ) / 3998768660480

def SurrogateDiagonalTailChunk000Sub000Block041Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1762
    = surrogateDiagTailX0RatChunk000Sub000Block041Part015

theorem surrogateDiagonalTailChunk000Sub000Block041Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part015] using hcert

def TailChunk000Sub000Block041Part016SupportExplicit : Finset ℕ :=
  ([1763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part016 : ℚ :=
  (11081525603 : ℚ) / 398376747417600

def SurrogateDiagonalTailChunk000Sub000Block041Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1763
    = surrogateDiagTailX0RatChunk000Sub000Block041Part016

theorem surrogateDiagonalTailChunk000Sub000Block041Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part016] using hcert

def TailChunk000Sub000Block041Part017SupportExplicit : Finset ℕ :=
  ([1765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part017 : ℚ :=
  (229116709325 : ℚ) / 4913686929997824

def SurrogateDiagonalTailChunk000Sub000Block041Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1765
    = surrogateDiagTailX0RatChunk000Sub000Block041Part017

theorem surrogateDiagonalTailChunk000Sub000Block041Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part017] using hcert

def TailChunk000Sub000Block041Part018SupportExplicit : Finset ℕ :=
  ([1766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part018 : ℚ :=
  (121728945125 : ℚ) / 756608478657444

def SurrogateDiagonalTailChunk000Sub000Block041Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1766
    = surrogateDiagTailX0RatChunk000Sub000Block041Part018

theorem surrogateDiagonalTailChunk000Sub000Block041Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part018] using hcert

def TailChunk000Sub000Block041Part019SupportExplicit : Finset ℕ :=
  ([1767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part019 : ℚ :=
  (14246312443 : ℚ) / 136076105779200

def SurrogateDiagonalTailChunk000Sub000Block041Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1767
    = surrogateDiagTailX0RatChunk000Sub000Block041Part019

theorem surrogateDiagonalTailChunk000Sub000Block041Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part019] using hcert

def TailChunk000Sub000Block041Part020SupportExplicit : Finset ℕ :=
  ([1769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part020 : ℚ :=
  (7408836287 : ℚ) / 265584498278400

def SurrogateDiagonalTailChunk000Sub000Block041Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1769
    = surrogateDiagTailX0RatChunk000Sub000Block041Part020

theorem surrogateDiagonalTailChunk000Sub000Block041Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part020] using hcert

def TailChunk000Sub000Block041Part021SupportExplicit : Finset ℕ :=
  ([1770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part021 : ℚ :=
  (74515087775 : ℚ) / 57952047611904

def SurrogateDiagonalTailChunk000Sub000Block041Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1770
    = surrogateDiagTailX0RatChunk000Sub000Block041Part021

theorem surrogateDiagonalTailChunk000Sub000Block041Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part021] using hcert

def TailChunk000Sub000Block041Part022SupportExplicit : Finset ℕ :=
  ([1771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part022 : ℚ :=
  (4317262969 : ℚ) / 75914123788800

def SurrogateDiagonalTailChunk000Sub000Block041Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1771
    = surrogateDiagTailX0RatChunk000Sub000Block041Part022

theorem surrogateDiagonalTailChunk000Sub000Block041Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part022] using hcert

def TailChunk000Sub000Block041Part023SupportExplicit : Finset ℕ :=
  ([1774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part023 : ℚ :=
  (98247778875 : ℚ) / 513618303133336

def SurrogateDiagonalTailChunk000Sub000Block041Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1774
    = surrogateDiagTailX0RatChunk000Sub000Block041Part023

theorem surrogateDiagonalTailChunk000Sub000Block041Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part023] using hcert

def TailChunk000Sub000Block041Part024SupportExplicit : Finset ℕ :=
  ([1777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block041Part024 : ℚ :=
  (65759706425 : ℚ) / 2764115556728832

def SurrogateDiagonalTailChunk000Sub000Block041Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1777
    = surrogateDiagTailX0RatChunk000Sub000Block041Part024

theorem surrogateDiagonalTailChunk000Sub000Block041Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block041Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block041Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block041Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block041Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block041Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block041HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block041Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block041Part000
    + surrogateDiagTailX0RatChunk000Sub000Block041Part001
    + surrogateDiagTailX0RatChunk000Sub000Block041Part002
    + surrogateDiagTailX0RatChunk000Sub000Block041Part003
    + surrogateDiagTailX0RatChunk000Sub000Block041Part004
    + surrogateDiagTailX0RatChunk000Sub000Block041Part005
    + surrogateDiagTailX0RatChunk000Sub000Block041Part006
    + surrogateDiagTailX0RatChunk000Sub000Block041Part007
    + surrogateDiagTailX0RatChunk000Sub000Block041Part008
    + surrogateDiagTailX0RatChunk000Sub000Block041Part009

def surrogateDiagonalTailChunk000Sub000Block041MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block041Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block041Part010
    + surrogateDiagTailX0RatChunk000Sub000Block041Part011
    + surrogateDiagTailX0RatChunk000Sub000Block041Part012
    + surrogateDiagTailX0RatChunk000Sub000Block041Part013
    + surrogateDiagTailX0RatChunk000Sub000Block041Part014
    + surrogateDiagTailX0RatChunk000Sub000Block041Part015
    + surrogateDiagTailX0RatChunk000Sub000Block041Part016
    + surrogateDiagTailX0RatChunk000Sub000Block041Part017
    + surrogateDiagTailX0RatChunk000Sub000Block041Part018
    + surrogateDiagTailX0RatChunk000Sub000Block041Part019

def surrogateDiagonalTailChunk000Sub000Block041TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block041Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block041Part020
    + surrogateDiagTailX0RatChunk000Sub000Block041Part021
    + surrogateDiagTailX0RatChunk000Sub000Block041Part022
    + surrogateDiagTailX0RatChunk000Sub000Block041Part023
    + surrogateDiagTailX0RatChunk000Sub000Block041Part024

def surrogateDiagonalTailChunk000Sub000Block041Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block041HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block041MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block041TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block041 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block041Part000
    + surrogateDiagTailX0RatChunk000Sub000Block041Part001
    + surrogateDiagTailX0RatChunk000Sub000Block041Part002
    + surrogateDiagTailX0RatChunk000Sub000Block041Part003
    + surrogateDiagTailX0RatChunk000Sub000Block041Part004
    + surrogateDiagTailX0RatChunk000Sub000Block041Part005
    + surrogateDiagTailX0RatChunk000Sub000Block041Part006
    + surrogateDiagTailX0RatChunk000Sub000Block041Part007
    + surrogateDiagTailX0RatChunk000Sub000Block041Part008
    + surrogateDiagTailX0RatChunk000Sub000Block041Part009
    + surrogateDiagTailX0RatChunk000Sub000Block041Part010
    + surrogateDiagTailX0RatChunk000Sub000Block041Part011
    + surrogateDiagTailX0RatChunk000Sub000Block041Part012
    + surrogateDiagTailX0RatChunk000Sub000Block041Part013
    + surrogateDiagTailX0RatChunk000Sub000Block041Part014
    + surrogateDiagTailX0RatChunk000Sub000Block041Part015
    + surrogateDiagTailX0RatChunk000Sub000Block041Part016
    + surrogateDiagTailX0RatChunk000Sub000Block041Part017
    + surrogateDiagTailX0RatChunk000Sub000Block041Part018
    + surrogateDiagTailX0RatChunk000Sub000Block041Part019
    + surrogateDiagTailX0RatChunk000Sub000Block041Part020
    + surrogateDiagTailX0RatChunk000Sub000Block041Part021
    + surrogateDiagTailX0RatChunk000Sub000Block041Part022
    + surrogateDiagTailX0RatChunk000Sub000Block041Part023
    + surrogateDiagTailX0RatChunk000Sub000Block041Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block041_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block041Head + surrogateDiagTailX0RatChunk000Sub000Block041Mid + surrogateDiagTailX0RatChunk000Sub000Block041Tail =
      surrogateDiagTailX0RatChunk000Sub000Block041 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block041Head surrogateDiagTailX0RatChunk000Sub000Block041Mid surrogateDiagTailX0RatChunk000Sub000Block041Tail surrogateDiagTailX0RatChunk000Sub000Block041
  ring

def SurrogateDiagonalTailChunk000Sub000Block041HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block041HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block041Head

def SurrogateDiagonalTailChunk000Sub000Block041MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block041MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block041Mid

def SurrogateDiagonalTailChunk000Sub000Block041TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block041TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block041Tail

theorem surrogateDiagonalTailChunk000Sub000Block041_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block041HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block041MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block041TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block041Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block041 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block041HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block041MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block041TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block041Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block041_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

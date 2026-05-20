import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [47,48). -/

/- Block 047 covers tail-support indices [1175,1200) and q from 1986 to 2026. -/

def TailChunk000Sub000Block047Part000SupportExplicit : Finset ℕ :=
  ([1986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part000 : ℚ :=
  (91027 : ℚ) / 210830400

def SurrogateDiagonalTailChunk000Sub000Block047Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1986
    = surrogateDiagTailX0RatChunk000Sub000Block047Part000

theorem surrogateDiagonalTailChunk000Sub000Block047Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part000] using hcert

def TailChunk000Sub000Block047Part001SupportExplicit : Finset ℕ :=
  ([1987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part001 : ℚ :=
  (82220619425 : ℚ) / 4322164839675912

def SurrogateDiagonalTailChunk000Sub000Block047Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1987
    = surrogateDiagTailX0RatChunk000Sub000Block047Part001

theorem surrogateDiagonalTailChunk000Sub000Block047Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part001] using hcert

def TailChunk000Sub000Block047Part002SupportExplicit : Finset ℕ :=
  ([1990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part002 : ℚ :=
  (123159501875 : ℚ) / 491923522151424

def SurrogateDiagonalTailChunk000Sub000Block047Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1990
    = surrogateDiagTailX0RatChunk000Sub000Block047Part002

theorem surrogateDiagonalTailChunk000Sub000Block047Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part002] using hcert

def TailChunk000Sub000Block047Part003SupportExplicit : Finset ℕ :=
  ([1991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part003 : ℚ :=
  (921682103 : ℚ) / 52498497600000

def SurrogateDiagonalTailChunk000Sub000Block047Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1991
    = surrogateDiagTailX0RatChunk000Sub000Block047Part003

theorem surrogateDiagonalTailChunk000Sub000Block047Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part003] using hcert

def TailChunk000Sub000Block047Part004SupportExplicit : Finset ℕ :=
  ([1993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part004 : ℚ :=
  (82717920425 : ℚ) / 4374633615132672

def SurrogateDiagonalTailChunk000Sub000Block047Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1993
    = surrogateDiagTailX0RatChunk000Sub000Block047Part004

theorem surrogateDiagonalTailChunk000Sub000Block047Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part004] using hcert

def TailChunk000Sub000Block047Part005SupportExplicit : Finset ℕ :=
  ([1994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part005 : ℚ :=
  (155189655125 : ℚ) / 1230365704256064

def SurrogateDiagonalTailChunk000Sub000Block047Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1994
    = surrogateDiagTailX0RatChunk000Sub000Block047Part005

theorem surrogateDiagonalTailChunk000Sub000Block047Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part005] using hcert

def TailChunk000Sub000Block047Part006SupportExplicit : Finset ℕ :=
  ([1995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part006 : ℚ :=
  (6013966475 : ℚ) / 29029569232896

def SurrogateDiagonalTailChunk000Sub000Block047Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1995
    = surrogateDiagTailX0RatChunk000Sub000Block047Part006

theorem surrogateDiagonalTailChunk000Sub000Block047Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part006] using hcert

def TailChunk000Sub000Block047Part007SupportExplicit : Finset ℕ :=
  ([1997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part007 : ℚ :=
  (498401424775 : ℚ) / 39688894912384128

def SurrogateDiagonalTailChunk000Sub000Block047Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1997
    = surrogateDiagTailX0RatChunk000Sub000Block047Part007

theorem surrogateDiagonalTailChunk000Sub000Block047Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part007] using hcert

def TailChunk000Sub000Block047Part008SupportExplicit : Finset ℕ :=
  ([1999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part008 : ℚ :=
  (499400224975 : ℚ) / 39848207888008008

def SurrogateDiagonalTailChunk000Sub000Block047Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1999
    = surrogateDiagTailX0RatChunk000Sub000Block047Part008

theorem surrogateDiagonalTailChunk000Sub000Block047Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part008] using hcert

def TailChunk000Sub000Block047Part009SupportExplicit : Finset ℕ :=
  ([2001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part009 : ℚ :=
  (61769669575 : ℚ) / 822946590326784

def SurrogateDiagonalTailChunk000Sub000Block047Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2001
    = surrogateDiagTailX0RatChunk000Sub000Block047Part009

theorem surrogateDiagonalTailChunk000Sub000Block047Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part009] using hcert

def TailChunk000Sub000Block047Part010SupportExplicit : Finset ℕ :=
  ([2002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part010 : ℚ :=
  (83432447 : ℚ) / 248881766400

def SurrogateDiagonalTailChunk000Sub000Block047Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2002
    = surrogateDiagTailX0RatChunk000Sub000Block047Part010

theorem surrogateDiagonalTailChunk000Sub000Block047Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part010] using hcert

def TailChunk000Sub000Block047Part011SupportExplicit : Finset ℕ :=
  ([2003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part011 : ℚ :=
  (5115311475 : ℚ) / 273253552435864

def SurrogateDiagonalTailChunk000Sub000Block047Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2003
    = surrogateDiagTailX0RatChunk000Sub000Block047Part011

theorem surrogateDiagonalTailChunk000Sub000Block047Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part011] using hcert

def TailChunk000Sub000Block047Part012SupportExplicit : Finset ℕ :=
  ([2005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part012 : ℚ :=
  (8626327031 : ℚ) / 327745536000000

def SurrogateDiagonalTailChunk000Sub000Block047Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2005
    = surrogateDiagTailX0RatChunk000Sub000Block047Part012

theorem surrogateDiagonalTailChunk000Sub000Block047Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part012] using hcert

def TailChunk000Sub000Block047Part013SupportExplicit : Finset ℕ :=
  ([2006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part013 : ℚ :=
  (96970452675 : ℚ) / 618155174526976

def SurrogateDiagonalTailChunk000Sub000Block047Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2006
    = surrogateDiagTailX0RatChunk000Sub000Block047Part013

theorem surrogateDiagonalTailChunk000Sub000Block047Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part013] using hcert

def TailChunk000Sub000Block047Part014SupportExplicit : Finset ℕ :=
  ([2010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part014 : ℚ :=
  (165845786275 : ℚ) / 194340156899328

def SurrogateDiagonalTailChunk000Sub000Block047Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2010
    = surrogateDiagTailX0RatChunk000Sub000Block047Part014

theorem surrogateDiagonalTailChunk000Sub000Block047Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part014] using hcert

def TailChunk000Sub000Block047Part015SupportExplicit : Finset ℕ :=
  ([2011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part015 : ℚ :=
  (3368752793 : ℚ) / 181396361017800

def SurrogateDiagonalTailChunk000Sub000Block047Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2011
    = surrogateDiagTailX0RatChunk000Sub000Block047Part015

theorem surrogateDiagonalTailChunk000Sub000Block047Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part015] using hcert

def TailChunk000Sub000Block047Part016SupportExplicit : Finset ℕ :=
  ([2013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part016 : ℚ :=
  (88662127 : ℚ) / 1382676480000

def SurrogateDiagonalTailChunk000Sub000Block047Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2013
    = surrogateDiagTailX0RatChunk000Sub000Block047Part016

theorem surrogateDiagonalTailChunk000Sub000Block047Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part016] using hcert

def TailChunk000Sub000Block047Part017SupportExplicit : Finset ℕ :=
  ([2014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part017 : ℚ :=
  (177021575 : ℚ) / 1153391992272

def SurrogateDiagonalTailChunk000Sub000Block047Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2014
    = surrogateDiagTailX0RatChunk000Sub000Block047Part017

theorem surrogateDiagonalTailChunk000Sub000Block047Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part017] using hcert

def TailChunk000Sub000Block047Part018SupportExplicit : Finset ℕ :=
  ([2015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part018 : ℚ :=
  (1059808223 : ℚ) / 28671179489280

def SurrogateDiagonalTailChunk000Sub000Block047Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2015
    = surrogateDiagTailX0RatChunk000Sub000Block047Part018

theorem surrogateDiagonalTailChunk000Sub000Block047Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part018] using hcert

def TailChunk000Sub000Block047Part019SupportExplicit : Finset ℕ :=
  ([2017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part019 : ℚ :=
  (1729022825 : ℚ) / 93659186331648

def SurrogateDiagonalTailChunk000Sub000Block047Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2017
    = surrogateDiagTailX0RatChunk000Sub000Block047Part019

theorem surrogateDiagonalTailChunk000Sub000Block047Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part019] using hcert

def TailChunk000Sub000Block047Part020SupportExplicit : Finset ℕ :=
  ([2018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part020 : ℚ :=
  (158947896125 : ℚ) / 1290740661633024

def SurrogateDiagonalTailChunk000Sub000Block047Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2018
    = surrogateDiagTailX0RatChunk000Sub000Block047Part020

theorem surrogateDiagonalTailChunk000Sub000Block047Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part020] using hcert

def TailChunk000Sub000Block047Part021SupportExplicit : Finset ℕ :=
  ([2019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part021 : ℚ :=
  (120130621825 : ℚ) / 2039688946778112

def SurrogateDiagonalTailChunk000Sub000Block047Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2019
    = surrogateDiagTailX0RatChunk000Sub000Block047Part021

theorem surrogateDiagonalTailChunk000Sub000Block047Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part021] using hcert

def TailChunk000Sub000Block047Part022SupportExplicit : Finset ℕ :=
  ([2021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part022 : ℚ :=
  (246698200325 : ℚ) / 17419085527201344

def SurrogateDiagonalTailChunk000Sub000Block047Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2021
    = surrogateDiagTailX0RatChunk000Sub000Block047Part022

theorem surrogateDiagonalTailChunk000Sub000Block047Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part022] using hcert

def TailChunk000Sub000Block047Part023SupportExplicit : Finset ℕ :=
  ([2022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part023 : ℚ :=
  (2358925 : ℚ) / 5664669696

def SurrogateDiagonalTailChunk000Sub000Block047Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2022
    = surrogateDiagTailX0RatChunk000Sub000Block047Part023

theorem surrogateDiagonalTailChunk000Sub000Block047Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part023] using hcert

def TailChunk000Sub000Block047Part024SupportExplicit : Finset ℕ :=
  ([2026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block047Part024 : ℚ :=
  (160210635125 : ℚ) / 1311350883653184

def SurrogateDiagonalTailChunk000Sub000Block047Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2026
    = surrogateDiagTailX0RatChunk000Sub000Block047Part024

theorem surrogateDiagonalTailChunk000Sub000Block047Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block047Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block047Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block047Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block047Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block047Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block047HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block047Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block047Part000
    + surrogateDiagTailX0RatChunk000Sub000Block047Part001
    + surrogateDiagTailX0RatChunk000Sub000Block047Part002
    + surrogateDiagTailX0RatChunk000Sub000Block047Part003
    + surrogateDiagTailX0RatChunk000Sub000Block047Part004
    + surrogateDiagTailX0RatChunk000Sub000Block047Part005
    + surrogateDiagTailX0RatChunk000Sub000Block047Part006
    + surrogateDiagTailX0RatChunk000Sub000Block047Part007
    + surrogateDiagTailX0RatChunk000Sub000Block047Part008
    + surrogateDiagTailX0RatChunk000Sub000Block047Part009

def surrogateDiagonalTailChunk000Sub000Block047MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block047Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block047Part010
    + surrogateDiagTailX0RatChunk000Sub000Block047Part011
    + surrogateDiagTailX0RatChunk000Sub000Block047Part012
    + surrogateDiagTailX0RatChunk000Sub000Block047Part013
    + surrogateDiagTailX0RatChunk000Sub000Block047Part014
    + surrogateDiagTailX0RatChunk000Sub000Block047Part015
    + surrogateDiagTailX0RatChunk000Sub000Block047Part016
    + surrogateDiagTailX0RatChunk000Sub000Block047Part017
    + surrogateDiagTailX0RatChunk000Sub000Block047Part018
    + surrogateDiagTailX0RatChunk000Sub000Block047Part019

def surrogateDiagonalTailChunk000Sub000Block047TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block047Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block047Part020
    + surrogateDiagTailX0RatChunk000Sub000Block047Part021
    + surrogateDiagTailX0RatChunk000Sub000Block047Part022
    + surrogateDiagTailX0RatChunk000Sub000Block047Part023
    + surrogateDiagTailX0RatChunk000Sub000Block047Part024

def surrogateDiagonalTailChunk000Sub000Block047Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block047HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block047MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block047TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block047 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block047Part000
    + surrogateDiagTailX0RatChunk000Sub000Block047Part001
    + surrogateDiagTailX0RatChunk000Sub000Block047Part002
    + surrogateDiagTailX0RatChunk000Sub000Block047Part003
    + surrogateDiagTailX0RatChunk000Sub000Block047Part004
    + surrogateDiagTailX0RatChunk000Sub000Block047Part005
    + surrogateDiagTailX0RatChunk000Sub000Block047Part006
    + surrogateDiagTailX0RatChunk000Sub000Block047Part007
    + surrogateDiagTailX0RatChunk000Sub000Block047Part008
    + surrogateDiagTailX0RatChunk000Sub000Block047Part009
    + surrogateDiagTailX0RatChunk000Sub000Block047Part010
    + surrogateDiagTailX0RatChunk000Sub000Block047Part011
    + surrogateDiagTailX0RatChunk000Sub000Block047Part012
    + surrogateDiagTailX0RatChunk000Sub000Block047Part013
    + surrogateDiagTailX0RatChunk000Sub000Block047Part014
    + surrogateDiagTailX0RatChunk000Sub000Block047Part015
    + surrogateDiagTailX0RatChunk000Sub000Block047Part016
    + surrogateDiagTailX0RatChunk000Sub000Block047Part017
    + surrogateDiagTailX0RatChunk000Sub000Block047Part018
    + surrogateDiagTailX0RatChunk000Sub000Block047Part019
    + surrogateDiagTailX0RatChunk000Sub000Block047Part020
    + surrogateDiagTailX0RatChunk000Sub000Block047Part021
    + surrogateDiagTailX0RatChunk000Sub000Block047Part022
    + surrogateDiagTailX0RatChunk000Sub000Block047Part023
    + surrogateDiagTailX0RatChunk000Sub000Block047Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block047_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block047Head + surrogateDiagTailX0RatChunk000Sub000Block047Mid + surrogateDiagTailX0RatChunk000Sub000Block047Tail =
      surrogateDiagTailX0RatChunk000Sub000Block047 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block047Head surrogateDiagTailX0RatChunk000Sub000Block047Mid surrogateDiagTailX0RatChunk000Sub000Block047Tail surrogateDiagTailX0RatChunk000Sub000Block047
  ring

def SurrogateDiagonalTailChunk000Sub000Block047HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block047HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block047Head

def SurrogateDiagonalTailChunk000Sub000Block047MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block047MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block047Mid

def SurrogateDiagonalTailChunk000Sub000Block047TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block047TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block047Tail

theorem surrogateDiagonalTailChunk000Sub000Block047_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block047HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block047MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block047TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block047Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block047 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block047HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block047MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block047TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block047Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block047_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

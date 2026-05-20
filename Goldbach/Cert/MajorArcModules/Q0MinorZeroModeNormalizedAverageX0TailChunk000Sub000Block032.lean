import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [32,33). -/

/- Block 032 covers tail-support indices [800,825) and q from 1363 to 1402. -/

def TailChunk000Sub000Block032Part000SupportExplicit : Finset ℕ :=
  ([1363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part000 : ℚ :=
  (145612457325 : ℚ) / 2293871345145856

def SurrogateDiagonalTailChunk000Sub000Block032Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1363
    = surrogateDiagTailX0RatChunk000Sub000Block032Part000

theorem surrogateDiagonalTailChunk000Sub000Block032Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part000] using hcert

def TailChunk000Sub000Block032Part001SupportExplicit : Finset ℕ :=
  ([1365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part001 : ℚ :=
  (9458826875 : ℚ) / 15291295727616

def SurrogateDiagonalTailChunk000Sub000Block032Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1365
    = surrogateDiagTailX0RatChunk000Sub000Block032Part001

theorem surrogateDiagonalTailChunk000Sub000Block032Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part001] using hcert

def TailChunk000Sub000Block032Part002SupportExplicit : Finset ℕ :=
  ([1366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part002 : ℚ :=
  (18531275525 : ℚ) / 49178091691608

def SurrogateDiagonalTailChunk000Sub000Block032Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1366
    = surrogateDiagTailX0RatChunk000Sub000Block032Part002

theorem surrogateDiagonalTailChunk000Sub000Block032Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part002] using hcert

def TailChunk000Sub000Block032Part003SupportExplicit : Finset ℕ :=
  ([1367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part003 : ℚ :=
  (233445973325 : ℚ) / 4353110190368484

def SurrogateDiagonalTailChunk000Sub000Block032Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1367
    = surrogateDiagTailX0RatChunk000Sub000Block032Part003

theorem surrogateDiagonalTailChunk000Sub000Block032Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part003] using hcert

def TailChunk000Sub000Block032Part004SupportExplicit : Finset ℕ :=
  ([1370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part004 : ℚ :=
  (182767663525 : ℚ) / 218989079298048

def SurrogateDiagonalTailChunk000Sub000Block032Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1370
    = surrogateDiagTailX0RatChunk000Sub000Block032Part004

theorem surrogateDiagonalTailChunk000Sub000Block032Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part004] using hcert

def TailChunk000Sub000Block032Part005SupportExplicit : Finset ℕ :=
  ([1371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part005 : ℚ :=
  (299588983225 : ℚ) / 1729841102880768

def SurrogateDiagonalTailChunk000Sub000Block032Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1371
    = surrogateDiagTailX0RatChunk000Sub000Block032Part005

theorem surrogateDiagonalTailChunk000Sub000Block032Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part005] using hcert

def TailChunk000Sub000Block032Part006SupportExplicit : Finset ℕ :=
  ([1373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part006 : ℚ :=
  (2403539475 : ℚ) / 60273438730624

def SurrogateDiagonalTailChunk000Sub000Block032Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1373
    = surrogateDiagTailX0RatChunk000Sub000Block032Part006

theorem surrogateDiagonalTailChunk000Sub000Block032Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part006] using hcert

def TailChunk000Sub000Block032Part007SupportExplicit : Finset ℕ :=
  ([1374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part007 : ℚ :=
  (2345369425 : ℚ) / 1689297952032

def SurrogateDiagonalTailChunk000Sub000Block032Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1374
    = surrogateDiagTailX0RatChunk000Sub000Block032Part007

theorem surrogateDiagonalTailChunk000Sub000Block032Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part007] using hcert

def TailChunk000Sub000Block032Part008SupportExplicit : Finset ℕ :=
  ([1378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part008 : ℚ :=
  (7872758275 : ℚ) / 15796249178112

def SurrogateDiagonalTailChunk000Sub000Block032Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1378
    = surrogateDiagTailX0RatChunk000Sub000Block032Part008

theorem surrogateDiagonalTailChunk000Sub000Block032Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part008] using hcert

def TailChunk000Sub000Block032Part009SupportExplicit : Finset ℕ :=
  ([1379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part009 : ℚ :=
  (44233813375 : ℚ) / 531390316972032

def SurrogateDiagonalTailChunk000Sub000Block032Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1379
    = surrogateDiagTailX0RatChunk000Sub000Block032Part009

theorem surrogateDiagonalTailChunk000Sub000Block032Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part009] using hcert

def TailChunk000Sub000Block032Part010SupportExplicit : Finset ℕ :=
  ([1381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part010 : ℚ :=
  (1588665113 : ℚ) / 40305163420800

def SurrogateDiagonalTailChunk000Sub000Block032Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1381
    = surrogateDiagTailX0RatChunk000Sub000Block032Part010

theorem surrogateDiagonalTailChunk000Sub000Block032Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part010] using hcert

def TailChunk000Sub000Block032Part011SupportExplicit : Finset ℕ :=
  ([1382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part011 : ℚ :=
  (8345890399 : ℚ) / 22671654424200

def SurrogateDiagonalTailChunk000Sub000Block032Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1382
    = surrogateDiagTailX0RatChunk000Sub000Block032Part011

theorem surrogateDiagonalTailChunk000Sub000Block032Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part011] using hcert

def TailChunk000Sub000Block032Part012SupportExplicit : Finset ℕ :=
  ([1383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part012 : ℚ :=
  (12194279629 : ℚ) / 71653623859200

def SurrogateDiagonalTailChunk000Sub000Block032Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1383
    = surrogateDiagTailX0RatChunk000Sub000Block032Part012

theorem surrogateDiagonalTailChunk000Sub000Block032Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part012] using hcert

def TailChunk000Sub000Block032Part013SupportExplicit : Finset ℕ :=
  ([1385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part013 : ℚ :=
  (18827599075 : ℚ) / 232157741303808

def SurrogateDiagonalTailChunk000Sub000Block032Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1385
    = surrogateDiagTailX0RatChunk000Sub000Block032Part013

theorem surrogateDiagonalTailChunk000Sub000Block032Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part013] using hcert

def TailChunk000Sub000Block032Part014SupportExplicit : Finset ℕ :=
  ([1387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part014 : ℚ :=
  (49584643175 : ℚ) / 783798369288192

def SurrogateDiagonalTailChunk000Sub000Block032Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1387
    = surrogateDiagTailX0RatChunk000Sub000Block032Part014

theorem surrogateDiagonalTailChunk000Sub000Block032Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part014] using hcert

def TailChunk000Sub000Block032Part015SupportExplicit : Finset ℕ :=
  ([1389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part015 : ℚ :=
  (307508247775 : ℚ) / 1822698112169088

def SurrogateDiagonalTailChunk000Sub000Block032Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1389
    = surrogateDiagTailX0RatChunk000Sub000Block032Part015

theorem surrogateDiagonalTailChunk000Sub000Block032Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part015] using hcert

def TailChunk000Sub000Block032Part016SupportExplicit : Finset ℕ :=
  ([1390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part016 : ℚ :=
  (169100995375 : ℚ) / 232157741303808

def SurrogateDiagonalTailChunk000Sub000Block032Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1390
    = surrogateDiagTailX0RatChunk000Sub000Block032Part016

theorem surrogateDiagonalTailChunk000Sub000Block032Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part016] using hcert

def TailChunk000Sub000Block032Part017SupportExplicit : Finset ℕ :=
  ([1391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part017 : ℚ :=
  (36540976625 : ℚ) / 545499124729344

def SurrogateDiagonalTailChunk000Sub000Block032Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1391
    = surrogateDiagTailX0RatChunk000Sub000Block032Part017

theorem surrogateDiagonalTailChunk000Sub000Block032Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part017] using hcert

def TailChunk000Sub000Block032Part018SupportExplicit : Finset ℕ :=
  ([1393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part018 : ℚ :=
  (45136900675 : ℚ) / 553413962420352

def SurrogateDiagonalTailChunk000Sub000Block032Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1393
    = surrogateDiagTailX0RatChunk000Sub000Block032Part018

theorem surrogateDiagonalTailChunk000Sub000Block032Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part018] using hcert

def TailChunk000Sub000Block032Part019SupportExplicit : Finset ℕ :=
  ([1394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part019 : ℚ :=
  (326029893 : ℚ) / 699190476800

def SurrogateDiagonalTailChunk000Sub000Block032Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1394
    = surrogateDiagTailX0RatChunk000Sub000Block032Part019

theorem surrogateDiagonalTailChunk000Sub000Block032Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part019] using hcert

def TailChunk000Sub000Block032Part020SupportExplicit : Finset ℕ :=
  ([1397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part020 : ℚ :=
  (3478491251 : ℚ) / 50419557095040

def SurrogateDiagonalTailChunk000Sub000Block032Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1397
    = surrogateDiagTailX0RatChunk000Sub000Block032Part020

theorem surrogateDiagonalTailChunk000Sub000Block032Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part020] using hcert

def TailChunk000Sub000Block032Part021SupportExplicit : Finset ℕ :=
  ([1398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part021 : ℚ :=
  (145302813775 : ℚ) / 115904095223808

def SurrogateDiagonalTailChunk000Sub000Block032Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1398
    = surrogateDiagTailX0RatChunk000Sub000Block032Part021

theorem surrogateDiagonalTailChunk000Sub000Block032Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part021] using hcert

def TailChunk000Sub000Block032Part022SupportExplicit : Finset ℕ :=
  ([1399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part022 : ℚ :=
  (40758710825 : ℚ) / 1061238592837512

def SurrogateDiagonalTailChunk000Sub000Block032Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1399
    = surrogateDiagTailX0RatChunk000Sub000Block032Part022

theorem surrogateDiagonalTailChunk000Sub000Block032Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part022] using hcert

def TailChunk000Sub000Block032Part023SupportExplicit : Finset ℕ :=
  ([1401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part023 : ℚ :=
  (312845268475 : ℚ) / 1886646387266688

def SurrogateDiagonalTailChunk000Sub000Block032Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1401
    = surrogateDiagTailX0RatChunk000Sub000Block032Part023

theorem surrogateDiagonalTailChunk000Sub000Block032Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part023] using hcert

def TailChunk000Sub000Block032Part024SupportExplicit : Finset ℕ :=
  ([1402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block032Part024 : ℚ :=
  (1227028297 : ℚ) / 3430686000000

def SurrogateDiagonalTailChunk000Sub000Block032Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1402
    = surrogateDiagTailX0RatChunk000Sub000Block032Part024

theorem surrogateDiagonalTailChunk000Sub000Block032Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block032Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block032Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block032Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block032Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block032Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block032HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block032Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block032Part000
    + surrogateDiagTailX0RatChunk000Sub000Block032Part001
    + surrogateDiagTailX0RatChunk000Sub000Block032Part002
    + surrogateDiagTailX0RatChunk000Sub000Block032Part003
    + surrogateDiagTailX0RatChunk000Sub000Block032Part004
    + surrogateDiagTailX0RatChunk000Sub000Block032Part005
    + surrogateDiagTailX0RatChunk000Sub000Block032Part006
    + surrogateDiagTailX0RatChunk000Sub000Block032Part007
    + surrogateDiagTailX0RatChunk000Sub000Block032Part008
    + surrogateDiagTailX0RatChunk000Sub000Block032Part009

def surrogateDiagonalTailChunk000Sub000Block032MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block032Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block032Part010
    + surrogateDiagTailX0RatChunk000Sub000Block032Part011
    + surrogateDiagTailX0RatChunk000Sub000Block032Part012
    + surrogateDiagTailX0RatChunk000Sub000Block032Part013
    + surrogateDiagTailX0RatChunk000Sub000Block032Part014
    + surrogateDiagTailX0RatChunk000Sub000Block032Part015
    + surrogateDiagTailX0RatChunk000Sub000Block032Part016
    + surrogateDiagTailX0RatChunk000Sub000Block032Part017
    + surrogateDiagTailX0RatChunk000Sub000Block032Part018
    + surrogateDiagTailX0RatChunk000Sub000Block032Part019

def surrogateDiagonalTailChunk000Sub000Block032TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block032Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block032Part020
    + surrogateDiagTailX0RatChunk000Sub000Block032Part021
    + surrogateDiagTailX0RatChunk000Sub000Block032Part022
    + surrogateDiagTailX0RatChunk000Sub000Block032Part023
    + surrogateDiagTailX0RatChunk000Sub000Block032Part024

def surrogateDiagonalTailChunk000Sub000Block032Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block032HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block032MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block032TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block032 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block032Part000
    + surrogateDiagTailX0RatChunk000Sub000Block032Part001
    + surrogateDiagTailX0RatChunk000Sub000Block032Part002
    + surrogateDiagTailX0RatChunk000Sub000Block032Part003
    + surrogateDiagTailX0RatChunk000Sub000Block032Part004
    + surrogateDiagTailX0RatChunk000Sub000Block032Part005
    + surrogateDiagTailX0RatChunk000Sub000Block032Part006
    + surrogateDiagTailX0RatChunk000Sub000Block032Part007
    + surrogateDiagTailX0RatChunk000Sub000Block032Part008
    + surrogateDiagTailX0RatChunk000Sub000Block032Part009
    + surrogateDiagTailX0RatChunk000Sub000Block032Part010
    + surrogateDiagTailX0RatChunk000Sub000Block032Part011
    + surrogateDiagTailX0RatChunk000Sub000Block032Part012
    + surrogateDiagTailX0RatChunk000Sub000Block032Part013
    + surrogateDiagTailX0RatChunk000Sub000Block032Part014
    + surrogateDiagTailX0RatChunk000Sub000Block032Part015
    + surrogateDiagTailX0RatChunk000Sub000Block032Part016
    + surrogateDiagTailX0RatChunk000Sub000Block032Part017
    + surrogateDiagTailX0RatChunk000Sub000Block032Part018
    + surrogateDiagTailX0RatChunk000Sub000Block032Part019
    + surrogateDiagTailX0RatChunk000Sub000Block032Part020
    + surrogateDiagTailX0RatChunk000Sub000Block032Part021
    + surrogateDiagTailX0RatChunk000Sub000Block032Part022
    + surrogateDiagTailX0RatChunk000Sub000Block032Part023
    + surrogateDiagTailX0RatChunk000Sub000Block032Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block032_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block032Head + surrogateDiagTailX0RatChunk000Sub000Block032Mid + surrogateDiagTailX0RatChunk000Sub000Block032Tail =
      surrogateDiagTailX0RatChunk000Sub000Block032 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block032Head surrogateDiagTailX0RatChunk000Sub000Block032Mid surrogateDiagTailX0RatChunk000Sub000Block032Tail surrogateDiagTailX0RatChunk000Sub000Block032
  ring

def SurrogateDiagonalTailChunk000Sub000Block032HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block032HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block032Head

def SurrogateDiagonalTailChunk000Sub000Block032MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block032MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block032Mid

def SurrogateDiagonalTailChunk000Sub000Block032TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block032TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block032Tail

theorem surrogateDiagonalTailChunk000Sub000Block032_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block032HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block032MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block032TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block032Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block032 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block032HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block032MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block032TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block032Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block032_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

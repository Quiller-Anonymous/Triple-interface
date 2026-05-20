import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [31,32). -/

/- Block 031 covers tail-support indices [775,800) and q from 1322 to 1362. -/

def TailChunk000Sub000Block031Part000SupportExplicit : Finset ℕ :=
  ([1322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part000 : ℚ :=
  (694267469 : ℚ) / 1725320995200

def SurrogateDiagonalTailChunk000Sub000Block031Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1322
    = surrogateDiagTailX0RatChunk000Sub000Block031Part000

theorem surrogateDiagonalTailChunk000Sub000Block031Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part000] using hcert

def TailChunk000Sub000Block031Part001SupportExplicit : Finset ℕ :=
  ([1326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part001 : ℚ :=
  (2441024825 : ℚ) / 1132688572416

def SurrogateDiagonalTailChunk000Sub000Block031Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1326
    = surrogateDiagTailX0RatChunk000Sub000Block031Part001

theorem surrogateDiagonalTailChunk000Sub000Block031Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part001] using hcert

def TailChunk000Sub000Block031Part002SupportExplicit : Finset ℕ :=
  ([1327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part002 : ℚ :=
  (219984055325 : ℚ) / 3865190998843044

def SurrogateDiagonalTailChunk000Sub000Block031Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1327
    = surrogateDiagTailX0RatChunk000Sub000Block031Part002

theorem surrogateDiagonalTailChunk000Sub000Block031Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part002] using hcert

def TailChunk000Sub000Block031Part003SupportExplicit : Finset ℕ :=
  ([1329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part003 : ℚ :=
  (244868028325 : ℚ) / 1526989036579968

def SurrogateDiagonalTailChunk000Sub000Block031Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1329
    = surrogateDiagTailX0RatChunk000Sub000Block031Part003

theorem surrogateDiagonalTailChunk000Sub000Block031Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part003] using hcert

def TailChunk000Sub000Block031Part004SupportExplicit : Finset ℕ :=
  ([1330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part004 : ℚ :=
  (46505423525 : ℚ) / 29029569232896

def SurrogateDiagonalTailChunk000Sub000Block031Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1330
    = surrogateDiagTailX0RatChunk000Sub000Block031Part004

theorem surrogateDiagonalTailChunk000Sub000Block031Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part004] using hcert

def TailChunk000Sub000Block031Part005SupportExplicit : Finset ℕ :=
  ([1333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part005 : ℚ :=
  (12779088169 : ℚ) / 252097785475200

def SurrogateDiagonalTailChunk000Sub000Block031Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1333
    = surrogateDiagTailX0RatChunk000Sub000Block031Part005

theorem surrogateDiagonalTailChunk000Sub000Block031Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part005] using hcert

def TailChunk000Sub000Block031Part006SupportExplicit : Finset ℕ :=
  ([1334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part006 : ℚ :=
  (102207136475 : ℚ) / 180019566633984

def SurrogateDiagonalTailChunk000Sub000Block031Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1334
    = surrogateDiagTailX0RatChunk000Sub000Block031Part006

theorem surrogateDiagonalTailChunk000Sub000Block031Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part006] using hcert

def TailChunk000Sub000Block031Part007SupportExplicit : Finset ℕ :=
  ([1335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part007 : ℚ :=
  (224669775175 : ℚ) / 614210866249728

def SurrogateDiagonalTailChunk000Sub000Block031Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1335
    = surrogateDiagTailX0RatChunk000Sub000Block031Part007

theorem surrogateDiagonalTailChunk000Sub000Block031Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part007] using hcert

def TailChunk000Sub000Block031Part008SupportExplicit : Finset ℕ :=
  ([1337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part008 : ℚ :=
  (37647499 : ℚ) / 422324488008

def SurrogateDiagonalTailChunk000Sub000Block031Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1337
    = surrogateDiagTailX0RatChunk000Sub000Block031Part008

theorem surrogateDiagonalTailChunk000Sub000Block031Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part008] using hcert

def TailChunk000Sub000Block031Part009SupportExplicit : Finset ℕ :=
  ([1338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part009 : ℚ :=
  (133099180525 : ℚ) / 97175937541248

def SurrogateDiagonalTailChunk000Sub000Block031Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1338
    = surrogateDiagTailX0RatChunk000Sub000Block031Part009

theorem surrogateDiagonalTailChunk000Sub000Block031Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part009] using hcert

def TailChunk000Sub000Block031Part010SupportExplicit : Finset ℕ :=
  ([1339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part010 : ℚ :=
  (22608280175 : ℚ) / 311802810172416

def SurrogateDiagonalTailChunk000Sub000Block031Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1339
    = surrogateDiagTailX0RatChunk000Sub000Block031Part010

theorem surrogateDiagonalTailChunk000Sub000Block031Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part010] using hcert

def TailChunk000Sub000Block031Part011SupportExplicit : Finset ℕ :=
  ([1342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part011 : ℚ :=
  (473303293 : ℚ) / 864172800000

def SurrogateDiagonalTailChunk000Sub000Block031Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1342
    = surrogateDiagTailX0RatChunk000Sub000Block031Part011

theorem surrogateDiagonalTailChunk000Sub000Block031Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part011] using hcert

def TailChunk000Sub000Block031Part012SupportExplicit : Finset ℕ :=
  ([1343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part012 : ℚ :=
  (52102827275 : ℚ) / 758219960549376

def SurrogateDiagonalTailChunk000Sub000Block031Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1343
    = surrogateDiagTailX0RatChunk000Sub000Block031Part012

theorem surrogateDiagonalTailChunk000Sub000Block031Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part012] using hcert

def TailChunk000Sub000Block031Part013SupportExplicit : Finset ℕ :=
  ([1345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part013 : ℚ :=
  (88986840025 : ℚ) / 825554994143232

def SurrogateDiagonalTailChunk000Sub000Block031Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1345
    = surrogateDiagTailX0RatChunk000Sub000Block031Part013

theorem surrogateDiagonalTailChunk000Sub000Block031Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part013] using hcert

def TailChunk000Sub000Block031Part014SupportExplicit : Finset ℕ :=
  ([1346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part014 : ℚ :=
  (56536862425 : ℚ) / 127480559173632

def SurrogateDiagonalTailChunk000Sub000Block031Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1346
    = surrogateDiagTailX0RatChunk000Sub000Block031Part014

theorem surrogateDiagonalTailChunk000Sub000Block031Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part014] using hcert

def TailChunk000Sub000Block031Part015SupportExplicit : Finset ℕ :=
  ([1347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part015 : ℚ :=
  (251544095725 : ℚ) / 1611606081404928

def SurrogateDiagonalTailChunk000Sub000Block031Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1347
    = surrogateDiagTailX0RatChunk000Sub000Block031Part015

theorem surrogateDiagonalTailChunk000Sub000Block031Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part015] using hcert

def TailChunk000Sub000Block031Part016SupportExplicit : Finset ℕ :=
  ([1349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part016 : ℚ :=
  (301951049 : ℚ) / 4501746169200

def SurrogateDiagonalTailChunk000Sub000Block031Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1349
    = surrogateDiagTailX0RatChunk000Sub000Block031Part016

theorem surrogateDiagonalTailChunk000Sub000Block031Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part016] using hcert

def TailChunk000Sub000Block031Part017SupportExplicit : Finset ℕ :=
  ([1351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part017 : ℚ :=
  (9491856875 : ℚ) / 137621661548544

def SurrogateDiagonalTailChunk000Sub000Block031Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1351
    = surrogateDiagTailX0RatChunk000Sub000Block031Part017

theorem surrogateDiagonalTailChunk000Sub000Block031Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part017] using hcert

def TailChunk000Sub000Block031Part018SupportExplicit : Finset ℕ :=
  ([1353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part018 : ℚ :=
  (1720351299 : ℚ) / 6828032000000

def SurrogateDiagonalTailChunk000Sub000Block031Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1353
    = surrogateDiagTailX0RatChunk000Sub000Block031Part018

theorem surrogateDiagonalTailChunk000Sub000Block031Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part018] using hcert

def TailChunk000Sub000Block031Part019SupportExplicit : Finset ℕ :=
  ([1354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part019 : ℚ :=
  (200278314775 : ℚ) / 522172074972288

def SurrogateDiagonalTailChunk000Sub000Block031Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1354
    = surrogateDiagTailX0RatChunk000Sub000Block031Part019

theorem surrogateDiagonalTailChunk000Sub000Block031Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part019] using hcert

def TailChunk000Sub000Block031Part020SupportExplicit : Finset ℕ :=
  ([1355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part020 : ℚ :=
  (5766802541 : ℚ) / 68038052889600

def SurrogateDiagonalTailChunk000Sub000Block031Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1355
    = surrogateDiagTailX0RatChunk000Sub000Block031Part020

theorem surrogateDiagonalTailChunk000Sub000Block031Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part020] using hcert

def TailChunk000Sub000Block031Part021SupportExplicit : Finset ℕ :=
  ([1357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part021 : ℚ :=
  (143631787725 : ℚ) / 2209572731994496

def SurrogateDiagonalTailChunk000Sub000Block031Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1357
    = surrogateDiagTailX0RatChunk000Sub000Block031Part021

theorem surrogateDiagonalTailChunk000Sub000Block031Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part021] using hcert

def TailChunk000Sub000Block031Part022SupportExplicit : Finset ℕ :=
  ([1358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part022 : ℚ :=
  (19217935975 : ℚ) / 30582591455232

def SurrogateDiagonalTailChunk000Sub000Block031Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1358
    = surrogateDiagTailX0RatChunk000Sub000Block031Part022

theorem surrogateDiagonalTailChunk000Sub000Block031Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part022] using hcert

def TailChunk000Sub000Block031Part023SupportExplicit : Finset ℕ :=
  ([1361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part023 : ℚ :=
  (9256048037 : ℚ) / 171085218201600

def SurrogateDiagonalTailChunk000Sub000Block031Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1361
    = surrogateDiagTailX0RatChunk000Sub000Block031Part023

theorem surrogateDiagonalTailChunk000Sub000Block031Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part023] using hcert

def TailChunk000Sub000Block031Part024SupportExplicit : Finset ℕ :=
  ([1362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block031Part024 : ℚ :=
  (137916121225 : ℚ) / 104371181102208

def SurrogateDiagonalTailChunk000Sub000Block031Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1362
    = surrogateDiagTailX0RatChunk000Sub000Block031Part024

theorem surrogateDiagonalTailChunk000Sub000Block031Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block031Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block031Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block031Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block031Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block031Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block031HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block031Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block031Part000
    + surrogateDiagTailX0RatChunk000Sub000Block031Part001
    + surrogateDiagTailX0RatChunk000Sub000Block031Part002
    + surrogateDiagTailX0RatChunk000Sub000Block031Part003
    + surrogateDiagTailX0RatChunk000Sub000Block031Part004
    + surrogateDiagTailX0RatChunk000Sub000Block031Part005
    + surrogateDiagTailX0RatChunk000Sub000Block031Part006
    + surrogateDiagTailX0RatChunk000Sub000Block031Part007
    + surrogateDiagTailX0RatChunk000Sub000Block031Part008
    + surrogateDiagTailX0RatChunk000Sub000Block031Part009

def surrogateDiagonalTailChunk000Sub000Block031MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block031Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block031Part010
    + surrogateDiagTailX0RatChunk000Sub000Block031Part011
    + surrogateDiagTailX0RatChunk000Sub000Block031Part012
    + surrogateDiagTailX0RatChunk000Sub000Block031Part013
    + surrogateDiagTailX0RatChunk000Sub000Block031Part014
    + surrogateDiagTailX0RatChunk000Sub000Block031Part015
    + surrogateDiagTailX0RatChunk000Sub000Block031Part016
    + surrogateDiagTailX0RatChunk000Sub000Block031Part017
    + surrogateDiagTailX0RatChunk000Sub000Block031Part018
    + surrogateDiagTailX0RatChunk000Sub000Block031Part019

def surrogateDiagonalTailChunk000Sub000Block031TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block031Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block031Part020
    + surrogateDiagTailX0RatChunk000Sub000Block031Part021
    + surrogateDiagTailX0RatChunk000Sub000Block031Part022
    + surrogateDiagTailX0RatChunk000Sub000Block031Part023
    + surrogateDiagTailX0RatChunk000Sub000Block031Part024

def surrogateDiagonalTailChunk000Sub000Block031Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block031HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block031MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block031TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block031 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block031Part000
    + surrogateDiagTailX0RatChunk000Sub000Block031Part001
    + surrogateDiagTailX0RatChunk000Sub000Block031Part002
    + surrogateDiagTailX0RatChunk000Sub000Block031Part003
    + surrogateDiagTailX0RatChunk000Sub000Block031Part004
    + surrogateDiagTailX0RatChunk000Sub000Block031Part005
    + surrogateDiagTailX0RatChunk000Sub000Block031Part006
    + surrogateDiagTailX0RatChunk000Sub000Block031Part007
    + surrogateDiagTailX0RatChunk000Sub000Block031Part008
    + surrogateDiagTailX0RatChunk000Sub000Block031Part009
    + surrogateDiagTailX0RatChunk000Sub000Block031Part010
    + surrogateDiagTailX0RatChunk000Sub000Block031Part011
    + surrogateDiagTailX0RatChunk000Sub000Block031Part012
    + surrogateDiagTailX0RatChunk000Sub000Block031Part013
    + surrogateDiagTailX0RatChunk000Sub000Block031Part014
    + surrogateDiagTailX0RatChunk000Sub000Block031Part015
    + surrogateDiagTailX0RatChunk000Sub000Block031Part016
    + surrogateDiagTailX0RatChunk000Sub000Block031Part017
    + surrogateDiagTailX0RatChunk000Sub000Block031Part018
    + surrogateDiagTailX0RatChunk000Sub000Block031Part019
    + surrogateDiagTailX0RatChunk000Sub000Block031Part020
    + surrogateDiagTailX0RatChunk000Sub000Block031Part021
    + surrogateDiagTailX0RatChunk000Sub000Block031Part022
    + surrogateDiagTailX0RatChunk000Sub000Block031Part023
    + surrogateDiagTailX0RatChunk000Sub000Block031Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block031_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block031Head + surrogateDiagTailX0RatChunk000Sub000Block031Mid + surrogateDiagTailX0RatChunk000Sub000Block031Tail =
      surrogateDiagTailX0RatChunk000Sub000Block031 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block031Head surrogateDiagTailX0RatChunk000Sub000Block031Mid surrogateDiagTailX0RatChunk000Sub000Block031Tail surrogateDiagTailX0RatChunk000Sub000Block031
  ring

def SurrogateDiagonalTailChunk000Sub000Block031HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block031HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block031Head

def SurrogateDiagonalTailChunk000Sub000Block031MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block031MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block031Mid

def SurrogateDiagonalTailChunk000Sub000Block031TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block031TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block031Tail

theorem surrogateDiagonalTailChunk000Sub000Block031_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block031HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block031MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block031TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block031Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block031 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block031HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block031MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block031TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block031Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block031_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

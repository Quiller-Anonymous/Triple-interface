import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [104,105). -/

/- Block 104 covers tail-support indices [2600,2625) and q from 4323 to 4366. -/

def TailChunk000Sub000Block104Part000SupportExplicit : Finset ℕ :=
  ([4323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part000 : ℚ :=
  (8165033203 : ℚ) / 1142668488000000

def SurrogateDiagonalTailChunk000Sub000Block104Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4323
    = surrogateDiagTailX0RatChunk000Sub000Block104Part000

theorem surrogateDiagonalTailChunk000Sub000Block104Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part000] using hcert

def TailChunk000Sub000Block104Part001SupportExplicit : Finset ℕ :=
  ([4326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part001 : ℚ :=
  (362068089925 : ℚ) / 5612450583103488

def SurrogateDiagonalTailChunk000Sub000Block104Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4326
    = surrogateDiagTailX0RatChunk000Sub000Block104Part001

theorem surrogateDiagonalTailChunk000Sub000Block104Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part001] using hcert

def TailChunk000Sub000Block104Part002SupportExplicit : Finset ℕ :=
  ([4327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part002 : ℚ :=
  (292545765625 : ℚ) / 218933856893385522

def SurrogateDiagonalTailChunk000Sub000Block104Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4327
    = surrogateDiagTailX0RatChunk000Sub000Block104Part002

theorem surrogateDiagonalTailChunk000Sub000Block104Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part002] using hcert

def TailChunk000Sub000Block104Part003SupportExplicit : Finset ℕ :=
  ([4330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part003 : ℚ :=
  (666207693775 : ℚ) / 22294709170864128

def SurrogateDiagonalTailChunk000Sub000Block104Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4330
    = surrogateDiagTailX0RatChunk000Sub000Block104Part003

theorem surrogateDiagonalTailChunk000Sub000Block104Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part003] using hcert

def TailChunk000Sub000Block104Part004SupportExplicit : Finset ℕ :=
  ([4331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part004 : ℚ :=
  (1827812299 : ℚ) / 1244927335680000

def SurrogateDiagonalTailChunk000Sub000Block104Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4331
    = surrogateDiagTailX0RatChunk000Sub000Block104Part004

theorem surrogateDiagonalTailChunk000Sub000Block104Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part004] using hcert

def TailChunk000Sub000Block104Part005SupportExplicit : Finset ℕ :=
  ([4333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part005 : ℚ :=
  (257123353825 : ℚ) / 118175043121127712

def SurrogateDiagonalTailChunk000Sub000Block104Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4333
    = surrogateDiagTailX0RatChunk000Sub000Block104Part005

theorem surrogateDiagonalTailChunk000Sub000Block104Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part005] using hcert

def TailChunk000Sub000Block104Part006SupportExplicit : Finset ℕ :=
  ([4334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part006 : ℚ :=
  (2155641 : ℚ) / 102463155200

def SurrogateDiagonalTailChunk000Sub000Block104Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4334
    = surrogateDiagTailX0RatChunk000Sub000Block104Part006

theorem surrogateDiagonalTailChunk000Sub000Block104Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part006] using hcert

def TailChunk000Sub000Block104Part007SupportExplicit : Finset ℕ :=
  ([4337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part007 : ℚ :=
  (293899515625 : ℚ) / 220965240713060352

def SurrogateDiagonalTailChunk000Sub000Block104Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4337
    = surrogateDiagTailX0RatChunk000Sub000Block104Part007

theorem surrogateDiagonalTailChunk000Sub000Block104Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part007] using hcert

def TailChunk000Sub000Block104Part008SupportExplicit : Finset ℕ :=
  ([4339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part008 : ℚ :=
  (294170640625 : ℚ) / 221373207815615442

def SurrogateDiagonalTailChunk000Sub000Block104Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4339
    = surrogateDiagTailX0RatChunk000Sub000Block104Part008

theorem surrogateDiagonalTailChunk000Sub000Block104Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part008] using hcert

def TailChunk000Sub000Block104Part009SupportExplicit : Finset ℕ :=
  ([4341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part009 : ℚ :=
  (26157275 : ℚ) / 5829239625408

def SurrogateDiagonalTailChunk000Sub000Block104Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4341
    = surrogateDiagTailX0RatChunk000Sub000Block104Part009

theorem surrogateDiagonalTailChunk000Sub000Block104Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part009] using hcert

def TailChunk000Sub000Block104Part010SupportExplicit : Finset ℕ :=
  ([4342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part010 : ℚ :=
  (17073394475 : ℚ) / 1230365704256064

def SurrogateDiagonalTailChunk000Sub000Block104Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4342
    = surrogateDiagTailX0RatChunk000Sub000Block104Part010

theorem surrogateDiagonalTailChunk000Sub000Block104Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part010] using hcert

def TailChunk000Sub000Block104Part011SupportExplicit : Finset ℕ :=
  ([4343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part011 : ℚ :=
  (9171509129 : ℚ) / 6224636678400000

def SurrogateDiagonalTailChunk000Sub000Block104Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4343
    = surrogateDiagTailX0RatChunk000Sub000Block104Part011

theorem surrogateDiagonalTailChunk000Sub000Block104Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part011] using hcert

def TailChunk000Sub000Block104Part012SupportExplicit : Finset ℕ :=
  ([4345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part012 : ℚ :=
  (4005233591 : ℚ) / 1053083278540800

def SurrogateDiagonalTailChunk000Sub000Block104Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4345
    = surrogateDiagTailX0RatChunk000Sub000Block104Part012

theorem surrogateDiagonalTailChunk000Sub000Block104Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part012] using hcert

def TailChunk000Sub000Block104Part013SupportExplicit : Finset ℕ :=
  ([4346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part013 : ℚ :=
  (7585652493 : ℚ) / 624049350246400

def SurrogateDiagonalTailChunk000Sub000Block104Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4346
    = surrogateDiagTailX0RatChunk000Sub000Block104Part013

theorem surrogateDiagonalTailChunk000Sub000Block104Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part013] using hcert

def TailChunk000Sub000Block104Part014SupportExplicit : Finset ℕ :=
  ([4349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part014 : ℚ :=
  (2363752279975 : ℚ) / 893686094605665408

def SurrogateDiagonalTailChunk000Sub000Block104Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4349
    = surrogateDiagTailX0RatChunk000Sub000Block104Part014

theorem surrogateDiagonalTailChunk000Sub000Block104Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part014] using hcert

def TailChunk000Sub000Block104Part015SupportExplicit : Finset ℕ :=
  ([4351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part015 : ℚ :=
  (2176179129625 : ℚ) / 709342967250044928

def SurrogateDiagonalTailChunk000Sub000Block104Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4351
    = surrogateDiagTailX0RatChunk000Sub000Block104Part015

theorem surrogateDiagonalTailChunk000Sub000Block104Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part015] using hcert

def TailChunk000Sub000Block104Part016SupportExplicit : Finset ℕ :=
  ([4353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part016 : ℚ :=
  (26296893347 : ℚ) / 3537112281000000

def SurrogateDiagonalTailChunk000Sub000Block104Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4353
    = surrogateDiagTailX0RatChunk000Sub000Block104Part016

theorem surrogateDiagonalTailChunk000Sub000Block104Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part016] using hcert

def TailChunk000Sub000Block104Part017SupportExplicit : Finset ℕ :=
  ([4354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part017 : ℚ :=
  (5185054543 : ℚ) / 299280648160800

def SurrogateDiagonalTailChunk000Sub000Block104Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4354
    = surrogateDiagTailX0RatChunk000Sub000Block104Part017

theorem surrogateDiagonalTailChunk000Sub000Block104Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part017] using hcert

def TailChunk000Sub000Block104Part018SupportExplicit : Finset ℕ :=
  ([4355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part018 : ℚ :=
  (437651137625 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub000Block104Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4355
    = surrogateDiagTailX0RatChunk000Sub000Block104Part018

theorem surrogateDiagonalTailChunk000Sub000Block104Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part018] using hcert

def TailChunk000Sub000Block104Part019SupportExplicit : Finset ℕ :=
  ([4357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part019 : ℚ :=
  (296616390625 : ℚ) / 225070383994343712

def SurrogateDiagonalTailChunk000Sub000Block104Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4357
    = surrogateDiagTailX0RatChunk000Sub000Block104Part019

theorem surrogateDiagonalTailChunk000Sub000Block104Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part019] using hcert

def TailChunk000Sub000Block104Part020SupportExplicit : Finset ℕ :=
  ([4358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part020 : ℚ :=
  (593386423975 : ℚ) / 56267595998585928

def SurrogateDiagonalTailChunk000Sub000Block104Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4358
    = surrogateDiagTailX0RatChunk000Sub000Block104Part020

theorem surrogateDiagonalTailChunk000Sub000Block104Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part020] using hcert

def TailChunk000Sub000Block104Part021SupportExplicit : Finset ℕ :=
  ([4359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part021 : ℚ :=
  (26374625 : ℚ) / 5926594341888

def SurrogateDiagonalTailChunk000Sub000Block104Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4359
    = surrogateDiagTailX0RatChunk000Sub000Block104Part021

theorem surrogateDiagonalTailChunk000Sub000Block104Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part021] using hcert

def TailChunk000Sub000Block104Part022SupportExplicit : Finset ℕ :=
  ([4362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part022 : ℚ :=
  (53619091325 : ℚ) / 1389323357989776

def SurrogateDiagonalTailChunk000Sub000Block104Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4362
    = surrogateDiagTailX0RatChunk000Sub000Block104Part022

theorem surrogateDiagonalTailChunk000Sub000Block104Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part022] using hcert

def TailChunk000Sub000Block104Part023SupportExplicit : Finset ℕ :=
  ([4363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part023 : ℚ :=
  (297433890625 : ℚ) / 226313005661632242

def SurrogateDiagonalTailChunk000Sub000Block104Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4363
    = surrogateDiagTailX0RatChunk000Sub000Block104Part023

theorem surrogateDiagonalTailChunk000Sub000Block104Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part023] using hcert

def TailChunk000Sub000Block104Part024SupportExplicit : Finset ℕ :=
  ([4366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block104Part024 : ℚ :=
  (573600217525 : ℚ) / 47527923047712768

def SurrogateDiagonalTailChunk000Sub000Block104Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4366
    = surrogateDiagTailX0RatChunk000Sub000Block104Part024

theorem surrogateDiagonalTailChunk000Sub000Block104Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block104Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block104Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block104Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block104Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block104Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block104HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block104Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block104Part000
    + surrogateDiagTailX0RatChunk000Sub000Block104Part001
    + surrogateDiagTailX0RatChunk000Sub000Block104Part002
    + surrogateDiagTailX0RatChunk000Sub000Block104Part003
    + surrogateDiagTailX0RatChunk000Sub000Block104Part004
    + surrogateDiagTailX0RatChunk000Sub000Block104Part005
    + surrogateDiagTailX0RatChunk000Sub000Block104Part006
    + surrogateDiagTailX0RatChunk000Sub000Block104Part007
    + surrogateDiagTailX0RatChunk000Sub000Block104Part008
    + surrogateDiagTailX0RatChunk000Sub000Block104Part009

def surrogateDiagonalTailChunk000Sub000Block104MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block104Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block104Part010
    + surrogateDiagTailX0RatChunk000Sub000Block104Part011
    + surrogateDiagTailX0RatChunk000Sub000Block104Part012
    + surrogateDiagTailX0RatChunk000Sub000Block104Part013
    + surrogateDiagTailX0RatChunk000Sub000Block104Part014
    + surrogateDiagTailX0RatChunk000Sub000Block104Part015
    + surrogateDiagTailX0RatChunk000Sub000Block104Part016
    + surrogateDiagTailX0RatChunk000Sub000Block104Part017
    + surrogateDiagTailX0RatChunk000Sub000Block104Part018
    + surrogateDiagTailX0RatChunk000Sub000Block104Part019

def surrogateDiagonalTailChunk000Sub000Block104TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block104Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block104Part020
    + surrogateDiagTailX0RatChunk000Sub000Block104Part021
    + surrogateDiagTailX0RatChunk000Sub000Block104Part022
    + surrogateDiagTailX0RatChunk000Sub000Block104Part023
    + surrogateDiagTailX0RatChunk000Sub000Block104Part024

def surrogateDiagonalTailChunk000Sub000Block104Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block104HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block104MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block104TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block104 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block104Part000
    + surrogateDiagTailX0RatChunk000Sub000Block104Part001
    + surrogateDiagTailX0RatChunk000Sub000Block104Part002
    + surrogateDiagTailX0RatChunk000Sub000Block104Part003
    + surrogateDiagTailX0RatChunk000Sub000Block104Part004
    + surrogateDiagTailX0RatChunk000Sub000Block104Part005
    + surrogateDiagTailX0RatChunk000Sub000Block104Part006
    + surrogateDiagTailX0RatChunk000Sub000Block104Part007
    + surrogateDiagTailX0RatChunk000Sub000Block104Part008
    + surrogateDiagTailX0RatChunk000Sub000Block104Part009
    + surrogateDiagTailX0RatChunk000Sub000Block104Part010
    + surrogateDiagTailX0RatChunk000Sub000Block104Part011
    + surrogateDiagTailX0RatChunk000Sub000Block104Part012
    + surrogateDiagTailX0RatChunk000Sub000Block104Part013
    + surrogateDiagTailX0RatChunk000Sub000Block104Part014
    + surrogateDiagTailX0RatChunk000Sub000Block104Part015
    + surrogateDiagTailX0RatChunk000Sub000Block104Part016
    + surrogateDiagTailX0RatChunk000Sub000Block104Part017
    + surrogateDiagTailX0RatChunk000Sub000Block104Part018
    + surrogateDiagTailX0RatChunk000Sub000Block104Part019
    + surrogateDiagTailX0RatChunk000Sub000Block104Part020
    + surrogateDiagTailX0RatChunk000Sub000Block104Part021
    + surrogateDiagTailX0RatChunk000Sub000Block104Part022
    + surrogateDiagTailX0RatChunk000Sub000Block104Part023
    + surrogateDiagTailX0RatChunk000Sub000Block104Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block104_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block104Head + surrogateDiagTailX0RatChunk000Sub000Block104Mid + surrogateDiagTailX0RatChunk000Sub000Block104Tail =
      surrogateDiagTailX0RatChunk000Sub000Block104 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block104Head surrogateDiagTailX0RatChunk000Sub000Block104Mid surrogateDiagTailX0RatChunk000Sub000Block104Tail surrogateDiagTailX0RatChunk000Sub000Block104
  ring

def SurrogateDiagonalTailChunk000Sub000Block104HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block104HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block104Head

def SurrogateDiagonalTailChunk000Sub000Block104MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block104MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block104Mid

def SurrogateDiagonalTailChunk000Sub000Block104TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block104TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block104Tail

theorem surrogateDiagonalTailChunk000Sub000Block104_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block104HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block104MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block104TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block104Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block104 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block104HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block104MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block104TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block104Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block104_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

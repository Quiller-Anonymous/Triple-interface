import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [105,106). -/

/- Block 105 covers tail-support indices [2625,2650) and q from 4367 to 4406. -/

def TailChunk000Sub000Block105Part000SupportExplicit : Finset ℕ :=
  ([4367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part000 : ℚ :=
  (14680601087 : ℚ) / 8198725369190400

def SurrogateDiagonalTailChunk000Sub000Block105Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4367
    = surrogateDiagTailX0RatChunk000Sub000Block105Part000

theorem surrogateDiagonalTailChunk000Sub000Block105Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part000] using hcert

def TailChunk000Sub000Block105Part001SupportExplicit : Finset ℕ :=
  ([4369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part001 : ℚ :=
  (281876813875 : ℚ) / 175957044816248832

def SurrogateDiagonalTailChunk000Sub000Block105Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4369
    = surrogateDiagTailX0RatChunk000Sub000Block105Part001

theorem surrogateDiagonalTailChunk000Sub000Block105Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part001] using hcert

def TailChunk000Sub000Block105Part002SupportExplicit : Finset ℕ :=
  ([4370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part002 : ℚ :=
  (49574468125 : ℚ) / 1311796059070464

def SurrogateDiagonalTailChunk000Sub000Block105Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4370
    = surrogateDiagTailX0RatChunk000Sub000Block105Part002

theorem surrogateDiagonalTailChunk000Sub000Block105Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part002] using hcert

def TailChunk000Sub000Block105Part003SupportExplicit : Finset ℕ :=
  ([4371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part003 : ℚ :=
  (30393462349 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub000Block105Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4371
    = surrogateDiagTailX0RatChunk000Sub000Block105Part003

theorem surrogateDiagonalTailChunk000Sub000Block105Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part003] using hcert

def TailChunk000Sub000Block105Part004SupportExplicit : Finset ℕ :=
  ([4373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part004 : ℚ :=
  (298798890625 : ℚ) / 228395467271622432

def SurrogateDiagonalTailChunk000Sub000Block105Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4373
    = surrogateDiagTailX0RatChunk000Sub000Block105Part004

theorem surrogateDiagonalTailChunk000Sub000Block105Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part004] using hcert

def TailChunk000Sub000Block105Part005SupportExplicit : Finset ℕ :=
  ([4377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part005 : ℚ :=
  (930805958275 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub000Block105Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4377
    = surrogateDiagTailX0RatChunk000Sub000Block105Part005

theorem surrogateDiagonalTailChunk000Sub000Block105Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part005] using hcert

def TailChunk000Sub000Block105Part006SupportExplicit : Finset ℕ :=
  ([4378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part006 : ℚ :=
  (21985003057 : ℚ) / 1537261006723200

def SurrogateDiagonalTailChunk000Sub000Block105Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4378
    = surrogateDiagTailX0RatChunk000Sub000Block105Part006

theorem surrogateDiagonalTailChunk000Sub000Block105Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part006] using hcert

def TailChunk000Sub000Block105Part007SupportExplicit : Finset ℕ :=
  ([4379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part007 : ℚ :=
  (73422583 : ℚ) / 49401878400000

def SurrogateDiagonalTailChunk000Sub000Block105Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4379
    = surrogateDiagTailX0RatChunk000Sub000Block105Part007

theorem surrogateDiagonalTailChunk000Sub000Block105Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part007] using hcert

def TailChunk000Sub000Block105Part008SupportExplicit : Finset ℕ :=
  ([4381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part008 : ℚ :=
  (124312177475 : ℚ) / 73428802084012032

def SurrogateDiagonalTailChunk000Sub000Block105Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4381
    = surrogateDiagTailX0RatChunk000Sub000Block105Part008

theorem surrogateDiagonalTailChunk000Sub000Block105Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part008] using hcert

def TailChunk000Sub000Block105Part009SupportExplicit : Finset ℕ :=
  ([4382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part009 : ℚ :=
  (131298307375 : ℚ) / 7676977100562432

def SurrogateDiagonalTailChunk000Sub000Block105Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4382
    = surrogateDiagTailX0RatChunk000Sub000Block105Part009

theorem surrogateDiagonalTailChunk000Sub000Block105Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part009] using hcert

def TailChunk000Sub000Block105Part010SupportExplicit : Finset ℕ :=
  ([4385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part010 : ℚ :=
  (480330921875 : ℚ) / 188474783539544064

def SurrogateDiagonalTailChunk000Sub000Block105Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4385
    = surrogateDiagTailX0RatChunk000Sub000Block105Part010

theorem surrogateDiagonalTailChunk000Sub000Block105Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part010] using hcert

def TailChunk000Sub000Block105Part011SupportExplicit : Finset ℕ :=
  ([4386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part011 : ℚ :=
  (60676950125 : ℚ) / 1019844473389056

def SurrogateDiagonalTailChunk000Sub000Block105Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4386
    = surrogateDiagTailX0RatChunk000Sub000Block105Part011

theorem surrogateDiagonalTailChunk000Sub000Block105Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part011] using hcert

def TailChunk000Sub000Block105Part012SupportExplicit : Finset ℕ :=
  ([4387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part012 : ℚ :=
  (30551818353 : ℚ) / 10775291352678400

def SurrogateDiagonalTailChunk000Sub000Block105Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4387
    = surrogateDiagTailX0RatChunk000Sub000Block105Part012

theorem surrogateDiagonalTailChunk000Sub000Block105Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part012] using hcert

def TailChunk000Sub000Block105Part013SupportExplicit : Finset ℕ :=
  ([4389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part013 : ℚ :=
  (11939557379 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub000Block105Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4389
    = surrogateDiagTailX0RatChunk000Sub000Block105Part013

theorem surrogateDiagonalTailChunk000Sub000Block105Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part013] using hcert

def TailChunk000Sub000Block105Part014SupportExplicit : Finset ℕ :=
  ([4390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part014 : ℚ :=
  (684807076225 : ℚ) / 23559347942443008

def SurrogateDiagonalTailChunk000Sub000Block105Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4390
    = surrogateDiagTailX0RatChunk000Sub000Block105Part014

theorem surrogateDiagonalTailChunk000Sub000Block105Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part014] using hcert

def TailChunk000Sub000Block105Part015SupportExplicit : Finset ℕ :=
  ([4391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part015 : ℚ :=
  (96385124119 : ℚ) / 37148812117768200

def SurrogateDiagonalTailChunk000Sub000Block105Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4391
    = surrogateDiagTailX0RatChunk000Sub000Block105Part015

theorem surrogateDiagonalTailChunk000Sub000Block105Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part015] using hcert

def TailChunk000Sub000Block105Part016SupportExplicit : Finset ℕ :=
  ([4393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part016 : ℚ :=
  (46219591117 : ℚ) / 30534581871235200

def SurrogateDiagonalTailChunk000Sub000Block105Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4393
    = surrogateDiagTailX0RatChunk000Sub000Block105Part016

theorem surrogateDiagonalTailChunk000Sub000Block105Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part016] using hcert

def TailChunk000Sub000Block105Part017SupportExplicit : Finset ℕ :=
  ([4395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part017 : ℚ :=
  (334375017425 : ℚ) / 37229586872008704

def SurrogateDiagonalTailChunk000Sub000Block105Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4395
    = surrogateDiagTailX0RatChunk000Sub000Block105Part017

theorem surrogateDiagonalTailChunk000Sub000Block105Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part017] using hcert

def TailChunk000Sub000Block105Part018SupportExplicit : Finset ℕ :=
  ([4397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part018 : ℚ :=
  (302087640625 : ℚ) / 233452001960339232

def SurrogateDiagonalTailChunk000Sub000Block105Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4397
    = surrogateDiagTailX0RatChunk000Sub000Block105Part018

theorem surrogateDiagonalTailChunk000Sub000Block105Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part018] using hcert

def TailChunk000Sub000Block105Part019SupportExplicit : Finset ℕ :=
  ([4398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part019 : ℚ :=
  (2981425 : ℚ) / 85068847104

def SurrogateDiagonalTailChunk000Sub000Block105Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4398
    = surrogateDiagTailX0RatChunk000Sub000Block105Part019

theorem surrogateDiagonalTailChunk000Sub000Block105Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part019] using hcert

def TailChunk000Sub000Block105Part020SupportExplicit : Finset ℕ :=
  ([4399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part020 : ℚ :=
  (392523475875 : ℚ) / 275533486875252736

def SurrogateDiagonalTailChunk000Sub000Block105Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4399
    = surrogateDiagTailX0RatChunk000Sub000Block105Part020

theorem surrogateDiagonalTailChunk000Sub000Block105Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part020] using hcert

def TailChunk000Sub000Block105Part021SupportExplicit : Finset ℕ :=
  ([4402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part021 : ℚ :=
  (3876195809 : ℚ) / 324199827000000

def SurrogateDiagonalTailChunk000Sub000Block105Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4402
    = surrogateDiagTailX0RatChunk000Sub000Block105Part021

theorem surrogateDiagonalTailChunk000Sub000Block105Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part021] using hcert

def TailChunk000Sub000Block105Part022SupportExplicit : Finset ℕ :=
  ([4403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part022 : ℚ :=
  (327470142175 : ℚ) / 118905115577942016

def SurrogateDiagonalTailChunk000Sub000Block105Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4403
    = surrogateDiagTailX0RatChunk000Sub000Block105Part022

theorem surrogateDiagonalTailChunk000Sub000Block105Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part022] using hcert

def TailChunk000Sub000Block105Part023SupportExplicit : Finset ℕ :=
  ([4405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part023 : ℚ :=
  (2714249139 : ℚ) / 1023684777082880

def SurrogateDiagonalTailChunk000Sub000Block105Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4405
    = surrogateDiagTailX0RatChunk000Sub000Block105Part023

theorem surrogateDiagonalTailChunk000Sub000Block105Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part023] using hcert

def TailChunk000Sub000Block105Part024SupportExplicit : Finset ℕ :=
  ([4406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block105Part024 : ℚ :=
  (101068077425 : ℚ) / 6532111780683912

def SurrogateDiagonalTailChunk000Sub000Block105Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4406
    = surrogateDiagTailX0RatChunk000Sub000Block105Part024

theorem surrogateDiagonalTailChunk000Sub000Block105Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block105Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block105Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block105Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block105Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block105Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block105HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block105Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block105Part000
    + surrogateDiagTailX0RatChunk000Sub000Block105Part001
    + surrogateDiagTailX0RatChunk000Sub000Block105Part002
    + surrogateDiagTailX0RatChunk000Sub000Block105Part003
    + surrogateDiagTailX0RatChunk000Sub000Block105Part004
    + surrogateDiagTailX0RatChunk000Sub000Block105Part005
    + surrogateDiagTailX0RatChunk000Sub000Block105Part006
    + surrogateDiagTailX0RatChunk000Sub000Block105Part007
    + surrogateDiagTailX0RatChunk000Sub000Block105Part008
    + surrogateDiagTailX0RatChunk000Sub000Block105Part009

def surrogateDiagonalTailChunk000Sub000Block105MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block105Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block105Part010
    + surrogateDiagTailX0RatChunk000Sub000Block105Part011
    + surrogateDiagTailX0RatChunk000Sub000Block105Part012
    + surrogateDiagTailX0RatChunk000Sub000Block105Part013
    + surrogateDiagTailX0RatChunk000Sub000Block105Part014
    + surrogateDiagTailX0RatChunk000Sub000Block105Part015
    + surrogateDiagTailX0RatChunk000Sub000Block105Part016
    + surrogateDiagTailX0RatChunk000Sub000Block105Part017
    + surrogateDiagTailX0RatChunk000Sub000Block105Part018
    + surrogateDiagTailX0RatChunk000Sub000Block105Part019

def surrogateDiagonalTailChunk000Sub000Block105TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block105Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block105Part020
    + surrogateDiagTailX0RatChunk000Sub000Block105Part021
    + surrogateDiagTailX0RatChunk000Sub000Block105Part022
    + surrogateDiagTailX0RatChunk000Sub000Block105Part023
    + surrogateDiagTailX0RatChunk000Sub000Block105Part024

def surrogateDiagonalTailChunk000Sub000Block105Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block105HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block105MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block105TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block105 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block105Part000
    + surrogateDiagTailX0RatChunk000Sub000Block105Part001
    + surrogateDiagTailX0RatChunk000Sub000Block105Part002
    + surrogateDiagTailX0RatChunk000Sub000Block105Part003
    + surrogateDiagTailX0RatChunk000Sub000Block105Part004
    + surrogateDiagTailX0RatChunk000Sub000Block105Part005
    + surrogateDiagTailX0RatChunk000Sub000Block105Part006
    + surrogateDiagTailX0RatChunk000Sub000Block105Part007
    + surrogateDiagTailX0RatChunk000Sub000Block105Part008
    + surrogateDiagTailX0RatChunk000Sub000Block105Part009
    + surrogateDiagTailX0RatChunk000Sub000Block105Part010
    + surrogateDiagTailX0RatChunk000Sub000Block105Part011
    + surrogateDiagTailX0RatChunk000Sub000Block105Part012
    + surrogateDiagTailX0RatChunk000Sub000Block105Part013
    + surrogateDiagTailX0RatChunk000Sub000Block105Part014
    + surrogateDiagTailX0RatChunk000Sub000Block105Part015
    + surrogateDiagTailX0RatChunk000Sub000Block105Part016
    + surrogateDiagTailX0RatChunk000Sub000Block105Part017
    + surrogateDiagTailX0RatChunk000Sub000Block105Part018
    + surrogateDiagTailX0RatChunk000Sub000Block105Part019
    + surrogateDiagTailX0RatChunk000Sub000Block105Part020
    + surrogateDiagTailX0RatChunk000Sub000Block105Part021
    + surrogateDiagTailX0RatChunk000Sub000Block105Part022
    + surrogateDiagTailX0RatChunk000Sub000Block105Part023
    + surrogateDiagTailX0RatChunk000Sub000Block105Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block105_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block105Head + surrogateDiagTailX0RatChunk000Sub000Block105Mid + surrogateDiagTailX0RatChunk000Sub000Block105Tail =
      surrogateDiagTailX0RatChunk000Sub000Block105 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block105Head surrogateDiagTailX0RatChunk000Sub000Block105Mid surrogateDiagTailX0RatChunk000Sub000Block105Tail surrogateDiagTailX0RatChunk000Sub000Block105
  ring

def SurrogateDiagonalTailChunk000Sub000Block105HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block105HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block105Head

def SurrogateDiagonalTailChunk000Sub000Block105MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block105MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block105Mid

def SurrogateDiagonalTailChunk000Sub000Block105TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block105TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block105Tail

theorem surrogateDiagonalTailChunk000Sub000Block105_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block105HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block105MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block105TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block105Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block105 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block105HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block105MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block105TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block105Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block105_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

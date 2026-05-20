import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [115,116). -/

/- Block 115 covers tail-support indices [2875,2900) and q from 4778 to 4818. -/

def TailChunk000Sub000Block115Part000SupportExplicit : Finset ℕ :=
  ([4778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part000 : ℚ :=
  (713272441975 : ℚ) / 81313779683875968

def SurrogateDiagonalTailChunk000Sub000Block115Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4778
    = surrogateDiagTailX0RatChunk000Sub000Block115Part000

theorem surrogateDiagonalTailChunk000Sub000Block115Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part000] using hcert

def TailChunk000Sub000Block115Part001SupportExplicit : Finset ℕ :=
  ([4781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part001 : ℚ :=
  (67948159825 : ℚ) / 38949048619753536

def SurrogateDiagonalTailChunk000Sub000Block115Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4781
    = surrogateDiagTailX0RatChunk000Sub000Block115Part001

theorem surrogateDiagonalTailChunk000Sub000Block115Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part001] using hcert

def TailChunk000Sub000Block115Part002SupportExplicit : Finset ℕ :=
  ([4782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part002 : ℚ :=
  (95167275 : ℚ) / 3211753883648

def SurrogateDiagonalTailChunk000Sub000Block115Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4782
    = surrogateDiagTailX0RatChunk000Sub000Block115Part002

theorem surrogateDiagonalTailChunk000Sub000Block115Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part002] using hcert

def TailChunk000Sub000Block115Part003SupportExplicit : Finset ℕ :=
  ([4783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part003 : ℚ :=
  (357454515625 : ℚ) / 326892649138346322

def SurrogateDiagonalTailChunk000Sub000Block115Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4783
    = surrogateDiagTailX0RatChunk000Sub000Block115Part003

theorem surrogateDiagonalTailChunk000Sub000Block115Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part003] using hcert

def TailChunk000Sub000Block115Part004SupportExplicit : Finset ℕ :=
  ([4785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part004 : ℚ :=
  (483756053 : ℚ) / 44966687539200

def SurrogateDiagonalTailChunk000Sub000Block115Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4785
    = surrogateDiagTailX0RatChunk000Sub000Block115Part004

theorem surrogateDiagonalTailChunk000Sub000Block115Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part004] using hcert

def TailChunk000Sub000Block115Part005SupportExplicit : Finset ℕ :=
  ([4786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part005 : ℚ :=
  (357759901275 : ℚ) / 27286655347234816

def SurrogateDiagonalTailChunk000Sub000Block115Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4786
    = surrogateDiagTailX0RatChunk000Sub000Block115Part005

theorem surrogateDiagonalTailChunk000Sub000Block115Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part005] using hcert

def TailChunk000Sub000Block115Part006SupportExplicit : Finset ℕ :=
  ([4787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part006 : ℚ :=
  (358052640625 : ℚ) / 327987765932309202

def SurrogateDiagonalTailChunk000Sub000Block115Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4787
    = surrogateDiagTailX0RatChunk000Sub000Block115Part006

theorem surrogateDiagonalTailChunk000Sub000Block115Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part006] using hcert

def TailChunk000Sub000Block115Part007SupportExplicit : Finset ℕ :=
  ([4789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part007 : ℚ :=
  (358351890625 : ℚ) / 328536355009135392

def SurrogateDiagonalTailChunk000Sub000Block115Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4789
    = surrogateDiagTailX0RatChunk000Sub000Block115Part007

theorem surrogateDiagonalTailChunk000Sub000Block115Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part007] using hcert

def TailChunk000Sub000Block115Part008SupportExplicit : Finset ℕ :=
  ([4790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part008 : ℚ :=
  (195617706375 : ℚ) / 11139280905312256

def SurrogateDiagonalTailChunk000Sub000Block115Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4790
    = surrogateDiagTailX0RatChunk000Sub000Block115Part008

theorem surrogateDiagonalTailChunk000Sub000Block115Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part008] using hcert

def TailChunk000Sub000Block115Part009SupportExplicit : Finset ℕ :=
  ([4791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part009 : ℚ :=
  (650225 : ℚ) / 176552635392

def SurrogateDiagonalTailChunk000Sub000Block115Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4791
    = surrogateDiagTailX0RatChunk000Sub000Block115Part009

theorem surrogateDiagonalTailChunk000Sub000Block115Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part009] using hcert

def TailChunk000Sub000Block115Part010SupportExplicit : Finset ℕ :=
  ([4793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part010 : ℚ :=
  (358950765625 : ℚ) / 329635597395251712

def SurrogateDiagonalTailChunk000Sub000Block115Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4793
    = surrogateDiagTailX0RatChunk000Sub000Block115Part010

theorem surrogateDiagonalTailChunk000Sub000Block115Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part010] using hcert

def TailChunk000Sub000Block115Part011SupportExplicit : Finset ℕ :=
  ([4794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part011 : ℚ :=
  (119044412275 : ℚ) / 2934932433272832

def SurrogateDiagonalTailChunk000Sub000Block115Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4794
    = surrogateDiagTailX0RatChunk000Sub000Block115Part011

theorem surrogateDiagonalTailChunk000Sub000Block115Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part011] using hcert

def TailChunk000Sub000Block115Part012SupportExplicit : Finset ℕ :=
  ([4795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part012 : ℚ :=
  (55463388125 : ℚ) / 15767213709459456

def SurrogateDiagonalTailChunk000Sub000Block115Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4795
    = surrogateDiagTailX0RatChunk000Sub000Block115Part012

theorem surrogateDiagonalTailChunk000Sub000Block115Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part012] using hcert

def TailChunk000Sub000Block115Part013SupportExplicit : Finset ℕ :=
  ([4798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part013 : ℚ :=
  (719256244975 : ℚ) / 82684398981121608

def SurrogateDiagonalTailChunk000Sub000Block115Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4798
    = surrogateDiagTailX0RatChunk000Sub000Block115Part013

theorem surrogateDiagonalTailChunk000Sub000Block115Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part013] using hcert

def TailChunk000Sub000Block115Part014SupportExplicit : Finset ℕ :=
  ([4799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part014 : ℚ :=
  (359850015625 : ℚ) / 331289630181110802

def SurrogateDiagonalTailChunk000Sub000Block115Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4799
    = surrogateDiagTailX0RatChunk000Sub000Block115Part014

theorem surrogateDiagonalTailChunk000Sub000Block115Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part014] using hcert

def TailChunk000Sub000Block115Part015SupportExplicit : Finset ℕ :=
  ([4801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part015 : ℚ :=
  (23049601 : ℚ) / 21237910732800

def SurrogateDiagonalTailChunk000Sub000Block115Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4801
    = surrogateDiagTailX0RatChunk000Sub000Block115Part015

theorem surrogateDiagonalTailChunk000Sub000Block115Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part015] using hcert

def TailChunk000Sub000Block115Part016SupportExplicit : Finset ℕ :=
  ([4803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part016 : ℚ :=
  (3842499 : ℚ) / 1048576000000

def SurrogateDiagonalTailChunk000Sub000Block115Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4803
    = surrogateDiagTailX0RatChunk000Sub000Block115Part016

theorem surrogateDiagonalTailChunk000Sub000Block115Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part016] using hcert

def TailChunk000Sub000Block115Part017SupportExplicit : Finset ℕ :=
  ([4807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part017 : ℚ :=
  (3985084897 : ℚ) / 2049681342297600

def SurrogateDiagonalTailChunk000Sub000Block115Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4807
    = surrogateDiagTailX0RatChunk000Sub000Block115Part017

theorem surrogateDiagonalTailChunk000Sub000Block115Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part017] using hcert

def TailChunk000Sub000Block115Part018SupportExplicit : Finset ℕ :=
  ([4809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part018 : ℚ :=
  (47795992475 : ℚ) / 5189523308642304

def SurrogateDiagonalTailChunk000Sub000Block115Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4809
    = surrogateDiagTailX0RatChunk000Sub000Block115Part018

theorem surrogateDiagonalTailChunk000Sub000Block115Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part018] using hcert

def TailChunk000Sub000Block115Part019SupportExplicit : Finset ℕ :=
  ([4810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part019 : ℚ :=
  (130446959125 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub000Block115Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4810
    = surrogateDiagTailX0RatChunk000Sub000Block115Part019

theorem surrogateDiagonalTailChunk000Sub000Block115Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part019] using hcert

def TailChunk000Sub000Block115Part020SupportExplicit : Finset ℕ :=
  ([4811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part020 : ℚ :=
  (1362130766875 : ℚ) / 1036342294825402368

def SurrogateDiagonalTailChunk000Sub000Block115Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4811
    = surrogateDiagTailX0RatChunk000Sub000Block115Part020

theorem surrogateDiagonalTailChunk000Sub000Block115Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part020] using hcert

def TailChunk000Sub000Block115Part021SupportExplicit : Finset ℕ :=
  ([4813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part021 : ℚ :=
  (361952640625 : ℚ) / 335173243593429792

def SurrogateDiagonalTailChunk000Sub000Block115Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4813
    = surrogateDiagTailX0RatChunk000Sub000Block115Part021

theorem surrogateDiagonalTailChunk000Sub000Block115Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part021] using hcert

def TailChunk000Sub000Block115Part022SupportExplicit : Finset ℕ :=
  ([4814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part022 : ℚ :=
  (32956799325 : ℚ) / 3308987290298368

def SurrogateDiagonalTailChunk000Sub000Block115Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4814
    = surrogateDiagTailX0RatChunk000Sub000Block115Part022

theorem surrogateDiagonalTailChunk000Sub000Block115Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part022] using hcert

def TailChunk000Sub000Block115Part023SupportExplicit : Finset ℕ :=
  ([4817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part023 : ℚ :=
  (362554515625 : ℚ) / 336289091962478592

def SurrogateDiagonalTailChunk000Sub000Block115Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4817
    = surrogateDiagTailX0RatChunk000Sub000Block115Part023

theorem surrogateDiagonalTailChunk000Sub000Block115Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part023] using hcert

def TailChunk000Sub000Block115Part024SupportExplicit : Finset ℕ :=
  ([4818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block115Part024 : ℚ :=
  (2897293241 : ℚ) / 71677948723200

def SurrogateDiagonalTailChunk000Sub000Block115Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4818
    = surrogateDiagTailX0RatChunk000Sub000Block115Part024

theorem surrogateDiagonalTailChunk000Sub000Block115Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block115Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block115Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block115Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block115Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block115Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block115HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block115Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block115Part000
    + surrogateDiagTailX0RatChunk000Sub000Block115Part001
    + surrogateDiagTailX0RatChunk000Sub000Block115Part002
    + surrogateDiagTailX0RatChunk000Sub000Block115Part003
    + surrogateDiagTailX0RatChunk000Sub000Block115Part004
    + surrogateDiagTailX0RatChunk000Sub000Block115Part005
    + surrogateDiagTailX0RatChunk000Sub000Block115Part006
    + surrogateDiagTailX0RatChunk000Sub000Block115Part007
    + surrogateDiagTailX0RatChunk000Sub000Block115Part008
    + surrogateDiagTailX0RatChunk000Sub000Block115Part009

def surrogateDiagonalTailChunk000Sub000Block115MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block115Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block115Part010
    + surrogateDiagTailX0RatChunk000Sub000Block115Part011
    + surrogateDiagTailX0RatChunk000Sub000Block115Part012
    + surrogateDiagTailX0RatChunk000Sub000Block115Part013
    + surrogateDiagTailX0RatChunk000Sub000Block115Part014
    + surrogateDiagTailX0RatChunk000Sub000Block115Part015
    + surrogateDiagTailX0RatChunk000Sub000Block115Part016
    + surrogateDiagTailX0RatChunk000Sub000Block115Part017
    + surrogateDiagTailX0RatChunk000Sub000Block115Part018
    + surrogateDiagTailX0RatChunk000Sub000Block115Part019

def surrogateDiagonalTailChunk000Sub000Block115TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block115Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block115Part020
    + surrogateDiagTailX0RatChunk000Sub000Block115Part021
    + surrogateDiagTailX0RatChunk000Sub000Block115Part022
    + surrogateDiagTailX0RatChunk000Sub000Block115Part023
    + surrogateDiagTailX0RatChunk000Sub000Block115Part024

def surrogateDiagonalTailChunk000Sub000Block115Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block115HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block115MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block115TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block115 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block115Part000
    + surrogateDiagTailX0RatChunk000Sub000Block115Part001
    + surrogateDiagTailX0RatChunk000Sub000Block115Part002
    + surrogateDiagTailX0RatChunk000Sub000Block115Part003
    + surrogateDiagTailX0RatChunk000Sub000Block115Part004
    + surrogateDiagTailX0RatChunk000Sub000Block115Part005
    + surrogateDiagTailX0RatChunk000Sub000Block115Part006
    + surrogateDiagTailX0RatChunk000Sub000Block115Part007
    + surrogateDiagTailX0RatChunk000Sub000Block115Part008
    + surrogateDiagTailX0RatChunk000Sub000Block115Part009
    + surrogateDiagTailX0RatChunk000Sub000Block115Part010
    + surrogateDiagTailX0RatChunk000Sub000Block115Part011
    + surrogateDiagTailX0RatChunk000Sub000Block115Part012
    + surrogateDiagTailX0RatChunk000Sub000Block115Part013
    + surrogateDiagTailX0RatChunk000Sub000Block115Part014
    + surrogateDiagTailX0RatChunk000Sub000Block115Part015
    + surrogateDiagTailX0RatChunk000Sub000Block115Part016
    + surrogateDiagTailX0RatChunk000Sub000Block115Part017
    + surrogateDiagTailX0RatChunk000Sub000Block115Part018
    + surrogateDiagTailX0RatChunk000Sub000Block115Part019
    + surrogateDiagTailX0RatChunk000Sub000Block115Part020
    + surrogateDiagTailX0RatChunk000Sub000Block115Part021
    + surrogateDiagTailX0RatChunk000Sub000Block115Part022
    + surrogateDiagTailX0RatChunk000Sub000Block115Part023
    + surrogateDiagTailX0RatChunk000Sub000Block115Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block115_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block115Head + surrogateDiagTailX0RatChunk000Sub000Block115Mid + surrogateDiagTailX0RatChunk000Sub000Block115Tail =
      surrogateDiagTailX0RatChunk000Sub000Block115 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block115Head surrogateDiagTailX0RatChunk000Sub000Block115Mid surrogateDiagTailX0RatChunk000Sub000Block115Tail surrogateDiagTailX0RatChunk000Sub000Block115
  ring

def SurrogateDiagonalTailChunk000Sub000Block115HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block115HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block115Head

def SurrogateDiagonalTailChunk000Sub000Block115MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block115MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block115Mid

def SurrogateDiagonalTailChunk000Sub000Block115TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block115TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block115Tail

theorem surrogateDiagonalTailChunk000Sub000Block115_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block115HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block115MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block115TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block115Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block115 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block115HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block115MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block115TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block115Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block115_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

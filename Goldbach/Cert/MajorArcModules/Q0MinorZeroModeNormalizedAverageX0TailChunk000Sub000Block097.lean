import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [97,98). -/

/- Block 097 covers tail-support indices [2425,2450) and q from 4038 to 4079. -/

def TailChunk000Sub000Block097Part000SupportExplicit : Finset ℕ :=
  ([4038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part000 : ℚ :=
  (120130621825 : ℚ) / 2039688946778112

def SurrogateDiagonalTailChunk000Sub000Block097Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4038
    = surrogateDiagTailX0RatChunk000Sub000Block097Part000

theorem surrogateDiagonalTailChunk000Sub000Block097Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part000] using hcert

def TailChunk000Sub000Block097Part001SupportExplicit : Finset ℕ :=
  ([4039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part001 : ℚ :=
  (410059311475 : ℚ) / 89178836683456512

def SurrogateDiagonalTailChunk000Sub000Block097Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4039
    = surrogateDiagTailX0RatChunk000Sub000Block097Part001

theorem surrogateDiagonalTailChunk000Sub000Block097Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part001] using hcert

def TailChunk000Sub000Block097Part002SupportExplicit : Finset ℕ :=
  ([4042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part002 : ℚ :=
  (246698200325 : ℚ) / 17419085527201344

def SurrogateDiagonalTailChunk000Sub000Block097Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4042
    = surrogateDiagTailX0RatChunk000Sub000Block097Part002

theorem surrogateDiagonalTailChunk000Sub000Block097Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part002] using hcert

def TailChunk000Sub000Block097Part003SupportExplicit : Finset ℕ :=
  ([4043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part003 : ℚ :=
  (19178361707 : ℚ) / 9576980741145600

def SurrogateDiagonalTailChunk000Sub000Block097Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4043
    = surrogateDiagTailX0RatChunk000Sub000Block097Part003

theorem surrogateDiagonalTailChunk000Sub000Block097Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part003] using hcert

def TailChunk000Sub000Block097Part004SupportExplicit : Finset ℕ :=
  ([4045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part004 : ℚ :=
  (286099017375 : ℚ) / 90947551738986496

def SurrogateDiagonalTailChunk000Sub000Block097Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4045
    = surrogateDiagTailX0RatChunk000Sub000Block097Part004

theorem surrogateDiagonalTailChunk000Sub000Block097Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part004] using hcert

def TailChunk000Sub000Block097Part005SupportExplicit : Finset ℕ :=
  ([4047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part005 : ℚ :=
  (29849685307 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block097Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4047
    = surrogateDiagTailX0RatChunk000Sub000Block097Part005

theorem surrogateDiagonalTailChunk000Sub000Block097Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part005] using hcert

def TailChunk000Sub000Block097Part006SupportExplicit : Finset ℕ :=
  ([4049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part006 : ℚ :=
  (256162515625 : ℚ) / 167852913107607552

def SurrogateDiagonalTailChunk000Sub000Block097Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4049
    = surrogateDiagTailX0RatChunk000Sub000Block097Part006

theorem surrogateDiagonalTailChunk000Sub000Block097Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part006] using hcert

def TailChunk000Sub000Block097Part007SupportExplicit : Finset ℕ :=
  ([4051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part007 : ℚ :=
  (16410601 : ℚ) / 10763832586050

def SurrogateDiagonalTailChunk000Sub000Block097Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4051
    = surrogateDiagTailX0RatChunk000Sub000Block097Part007

theorem surrogateDiagonalTailChunk000Sub000Block097Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part007] using hcert

def TailChunk000Sub000Block097Part008SupportExplicit : Finset ℕ :=
  ([4053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part008 : ℚ :=
  (609805908775 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block097Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4053
    = surrogateDiagTailX0RatChunk000Sub000Block097Part008

theorem surrogateDiagonalTailChunk000Sub000Block097Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part008] using hcert

def TailChunk000Sub000Block097Part009SupportExplicit : Finset ℕ :=
  ([4054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part009 : ℚ :=
  (256692844275 : ℚ) / 14043112281657496

def SurrogateDiagonalTailChunk000Sub000Block097Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4054
    = surrogateDiagTailX0RatChunk000Sub000Block097Part009

theorem surrogateDiagonalTailChunk000Sub000Block097Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part009] using hcert

def TailChunk000Sub000Block097Part010SupportExplicit : Finset ℕ :=
  ([4055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part010 : ℚ :=
  (6900360887 : ℚ) / 2204432913623040

def SurrogateDiagonalTailChunk000Sub000Block097Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4055
    = surrogateDiagTailX0RatChunk000Sub000Block097Part010

theorem surrogateDiagonalTailChunk000Sub000Block097Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part010] using hcert

def TailChunk000Sub000Block097Part011SupportExplicit : Finset ℕ :=
  ([4057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part011 : ℚ :=
  (257175765625 : ℚ) / 169183752291021312

def SurrogateDiagonalTailChunk000Sub000Block097Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4057
    = surrogateDiagTailX0RatChunk000Sub000Block097Part011

theorem surrogateDiagonalTailChunk000Sub000Block097Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part011] using hcert

def TailChunk000Sub000Block097Part012SupportExplicit : Finset ℕ :=
  ([4058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part012 : ℚ :=
  (514502203975 : ℚ) / 42295938072755328

def SurrogateDiagonalTailChunk000Sub000Block097Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4058
    = surrogateDiagTailX0RatChunk000Sub000Block097Part012

theorem surrogateDiagonalTailChunk000Sub000Block097Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part012] using hcert

def TailChunk000Sub000Block097Part013SupportExplicit : Finset ℕ :=
  ([4061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part013 : ℚ :=
  (39967838227 : ℚ) / 23139036882000000

def SurrogateDiagonalTailChunk000Sub000Block097Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4061
    = surrogateDiagTailX0RatChunk000Sub000Block097Part013

theorem surrogateDiagonalTailChunk000Sub000Block097Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part013] using hcert

def TailChunk000Sub000Block097Part014SupportExplicit : Finset ℕ :=
  ([4062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part014 : ℚ :=
  (185992983425 : ℚ) / 4177376599778304

def SurrogateDiagonalTailChunk000Sub000Block097Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4062
    = surrogateDiagTailX0RatChunk000Sub000Block097Part014

theorem surrogateDiagonalTailChunk000Sub000Block097Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part014] using hcert

def TailChunk000Sub000Block097Part015SupportExplicit : Finset ℕ :=
  ([4063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part015 : ℚ :=
  (4797740625 : ℚ) / 2577415585267712

def SurrogateDiagonalTailChunk000Sub000Block097Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4063
    = surrogateDiagTailX0RatChunk000Sub000Block097Part015

theorem surrogateDiagonalTailChunk000Sub000Block097Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part015] using hcert

def TailChunk000Sub000Block097Part016SupportExplicit : Finset ℕ :=
  ([4065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part016 : ℚ :=
  (5766950647 : ℚ) / 544304423116800

def SurrogateDiagonalTailChunk000Sub000Block097Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4065
    = surrogateDiagTailX0RatChunk000Sub000Block097Part016

theorem surrogateDiagonalTailChunk000Sub000Block097Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part016] using hcert

def TailChunk000Sub000Block097Part017SupportExplicit : Finset ℕ :=
  ([4066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part017 : ℚ :=
  (239724588475 : ℚ) / 11046357275769216

def SurrogateDiagonalTailChunk000Sub000Block097Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4066
    = surrogateDiagTailX0RatChunk000Sub000Block097Part017

theorem surrogateDiagonalTailChunk000Sub000Block097Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part017] using hcert

def TailChunk000Sub000Block097Part018SupportExplicit : Finset ℕ :=
  ([4069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part018 : ℚ :=
  (204594299675 : ℚ) / 54591837159555072

def SurrogateDiagonalTailChunk000Sub000Block097Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4069
    = surrogateDiagTailX0RatChunk000Sub000Block097Part018

theorem surrogateDiagonalTailChunk000Sub000Block097Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part018] using hcert

def TailChunk000Sub000Block097Part019SupportExplicit : Finset ℕ :=
  ([4070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part019 : ℚ :=
  (10260652889 : ℚ) / 215033846169600

def SurrogateDiagonalTailChunk000Sub000Block097Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4070
    = surrogateDiagTailX0RatChunk000Sub000Block097Part019

theorem surrogateDiagonalTailChunk000Sub000Block097Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part019] using hcert

def TailChunk000Sub000Block097Part020SupportExplicit : Finset ℕ :=
  ([4071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part020 : ℚ :=
  (32278226025 : ℚ) / 3213923973810176

def SurrogateDiagonalTailChunk000Sub000Block097Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4071
    = surrogateDiagTailX0RatChunk000Sub000Block097Part020

theorem surrogateDiagonalTailChunk000Sub000Block097Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part020] using hcert

def TailChunk000Sub000Block097Part021SupportExplicit : Finset ℕ :=
  ([4073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part021 : ℚ :=
  (259208265625 : ℚ) / 171869156234015232

def SurrogateDiagonalTailChunk000Sub000Block097Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4073
    = surrogateDiagTailX0RatChunk000Sub000Block097Part021

theorem surrogateDiagonalTailChunk000Sub000Block097Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part021] using hcert

def TailChunk000Sub000Block097Part022SupportExplicit : Finset ℕ :=
  ([4074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part022 : ℚ :=
  (2007301175 : ℚ) / 27184525737984

def SurrogateDiagonalTailChunk000Sub000Block097Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4074
    = surrogateDiagTailX0RatChunk000Sub000Block097Part022

theorem surrogateDiagonalTailChunk000Sub000Block097Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part022] using hcert

def TailChunk000Sub000Block097Part023SupportExplicit : Finset ℕ :=
  ([4078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part023 : ℚ :=
  (519586186975 : ℚ) / 43136368201370568

def SurrogateDiagonalTailChunk000Sub000Block097Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4078
    = surrogateDiagTailX0RatChunk000Sub000Block097Part023

theorem surrogateDiagonalTailChunk000Sub000Block097Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part023] using hcert

def TailChunk000Sub000Block097Part024SupportExplicit : Finset ℕ :=
  ([4079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block097Part024 : ℚ :=
  (259972515625 : ℚ) / 172884378616140882

def SurrogateDiagonalTailChunk000Sub000Block097Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4079
    = surrogateDiagTailX0RatChunk000Sub000Block097Part024

theorem surrogateDiagonalTailChunk000Sub000Block097Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block097Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block097Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block097Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block097Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block097Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block097HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block097Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block097Part000
    + surrogateDiagTailX0RatChunk000Sub000Block097Part001
    + surrogateDiagTailX0RatChunk000Sub000Block097Part002
    + surrogateDiagTailX0RatChunk000Sub000Block097Part003
    + surrogateDiagTailX0RatChunk000Sub000Block097Part004
    + surrogateDiagTailX0RatChunk000Sub000Block097Part005
    + surrogateDiagTailX0RatChunk000Sub000Block097Part006
    + surrogateDiagTailX0RatChunk000Sub000Block097Part007
    + surrogateDiagTailX0RatChunk000Sub000Block097Part008
    + surrogateDiagTailX0RatChunk000Sub000Block097Part009

def surrogateDiagonalTailChunk000Sub000Block097MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block097Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block097Part010
    + surrogateDiagTailX0RatChunk000Sub000Block097Part011
    + surrogateDiagTailX0RatChunk000Sub000Block097Part012
    + surrogateDiagTailX0RatChunk000Sub000Block097Part013
    + surrogateDiagTailX0RatChunk000Sub000Block097Part014
    + surrogateDiagTailX0RatChunk000Sub000Block097Part015
    + surrogateDiagTailX0RatChunk000Sub000Block097Part016
    + surrogateDiagTailX0RatChunk000Sub000Block097Part017
    + surrogateDiagTailX0RatChunk000Sub000Block097Part018
    + surrogateDiagTailX0RatChunk000Sub000Block097Part019

def surrogateDiagonalTailChunk000Sub000Block097TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block097Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block097Part020
    + surrogateDiagTailX0RatChunk000Sub000Block097Part021
    + surrogateDiagTailX0RatChunk000Sub000Block097Part022
    + surrogateDiagTailX0RatChunk000Sub000Block097Part023
    + surrogateDiagTailX0RatChunk000Sub000Block097Part024

def surrogateDiagonalTailChunk000Sub000Block097Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block097HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block097MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block097TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block097 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block097Part000
    + surrogateDiagTailX0RatChunk000Sub000Block097Part001
    + surrogateDiagTailX0RatChunk000Sub000Block097Part002
    + surrogateDiagTailX0RatChunk000Sub000Block097Part003
    + surrogateDiagTailX0RatChunk000Sub000Block097Part004
    + surrogateDiagTailX0RatChunk000Sub000Block097Part005
    + surrogateDiagTailX0RatChunk000Sub000Block097Part006
    + surrogateDiagTailX0RatChunk000Sub000Block097Part007
    + surrogateDiagTailX0RatChunk000Sub000Block097Part008
    + surrogateDiagTailX0RatChunk000Sub000Block097Part009
    + surrogateDiagTailX0RatChunk000Sub000Block097Part010
    + surrogateDiagTailX0RatChunk000Sub000Block097Part011
    + surrogateDiagTailX0RatChunk000Sub000Block097Part012
    + surrogateDiagTailX0RatChunk000Sub000Block097Part013
    + surrogateDiagTailX0RatChunk000Sub000Block097Part014
    + surrogateDiagTailX0RatChunk000Sub000Block097Part015
    + surrogateDiagTailX0RatChunk000Sub000Block097Part016
    + surrogateDiagTailX0RatChunk000Sub000Block097Part017
    + surrogateDiagTailX0RatChunk000Sub000Block097Part018
    + surrogateDiagTailX0RatChunk000Sub000Block097Part019
    + surrogateDiagTailX0RatChunk000Sub000Block097Part020
    + surrogateDiagTailX0RatChunk000Sub000Block097Part021
    + surrogateDiagTailX0RatChunk000Sub000Block097Part022
    + surrogateDiagTailX0RatChunk000Sub000Block097Part023
    + surrogateDiagTailX0RatChunk000Sub000Block097Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block097_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block097Head + surrogateDiagTailX0RatChunk000Sub000Block097Mid + surrogateDiagTailX0RatChunk000Sub000Block097Tail =
      surrogateDiagTailX0RatChunk000Sub000Block097 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block097Head surrogateDiagTailX0RatChunk000Sub000Block097Mid surrogateDiagTailX0RatChunk000Sub000Block097Tail surrogateDiagTailX0RatChunk000Sub000Block097
  ring

def SurrogateDiagonalTailChunk000Sub000Block097HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block097HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block097Head

def SurrogateDiagonalTailChunk000Sub000Block097MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block097MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block097Mid

def SurrogateDiagonalTailChunk000Sub000Block097TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block097TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block097Tail

theorem surrogateDiagonalTailChunk000Sub000Block097_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block097HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block097MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block097TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block097Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block097 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block097HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block097MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block097TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block097Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block097_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

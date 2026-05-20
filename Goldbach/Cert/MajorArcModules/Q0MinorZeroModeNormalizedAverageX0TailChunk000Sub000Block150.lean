import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [150,151). -/

/- Block 150 covers tail-support indices [3750,3775) and q from 6217 to 6261. -/

def TailChunk000Sub000Block150Part000SupportExplicit : Finset ℕ :=
  ([6217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part000 : ℚ :=
  (603923265625 : ℚ) / 933277704146145792

def SurrogateDiagonalTailChunk000Sub000Block150Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6217
    = surrogateDiagTailX0RatChunk000Sub000Block150Part000

theorem surrogateDiagonalTailChunk000Sub000Block150Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part000] using hcert

def TailChunk000Sub000Block150Part001SupportExplicit : Finset ℕ :=
  ([6218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part001 : ℚ :=
  (1207993477975 : ℚ) / 233319426036536448

def SurrogateDiagonalTailChunk000Sub000Block150Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6218
    = surrogateDiagTailX0RatChunk000Sub000Block150Part001

theorem surrogateDiagonalTailChunk000Sub000Block150Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part001] using hcert

def TailChunk000Sub000Block150Part002SupportExplicit : Finset ℕ :=
  ([6221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part002 : ℚ :=
  (967521025 : ℚ) / 1497091653018912

def SurrogateDiagonalTailChunk000Sub000Block150Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6221
    = surrogateDiagTailX0RatChunk000Sub000Block150Part002

theorem surrogateDiagonalTailChunk000Sub000Block150Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part002] using hcert

def TailChunk000Sub000Block150Part003SupportExplicit : Finset ℕ :=
  ([6222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part003 : ℚ :=
  (12406377701 : ℚ) / 679613143449600

def SurrogateDiagonalTailChunk000Sub000Block150Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6222
    = surrogateDiagTailX0RatChunk000Sub000Block150Part003

theorem surrogateDiagonalTailChunk000Sub000Block150Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part003] using hcert

def TailChunk000Sub000Block150Part004SupportExplicit : Finset ℕ :=
  ([6226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part004 : ℚ :=
  (319077869 : ℚ) / 46854306587520

def SurrogateDiagonalTailChunk000Sub000Block150Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6226
    = surrogateDiagTailX0RatChunk000Sub000Block150Part004

theorem surrogateDiagonalTailChunk000Sub000Block150Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part004] using hcert

def TailChunk000Sub000Block150Part005SupportExplicit : Finset ℕ :=
  ([6227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part005 : ℚ :=
  (734443859675 : ℚ) / 902281753330292736

def SurrogateDiagonalTailChunk000Sub000Block150Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6227
    = surrogateDiagTailX0RatChunk000Sub000Block150Part005

theorem surrogateDiagonalTailChunk000Sub000Block150Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part005] using hcert

def TailChunk000Sub000Block150Part006SupportExplicit : Finset ℕ :=
  ([6229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part006 : ℚ :=
  (606256890625 : ℚ) / 940505377703008032

def SurrogateDiagonalTailChunk000Sub000Block150Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6229
    = surrogateDiagTailX0RatChunk000Sub000Block150Part006

theorem surrogateDiagonalTailChunk000Sub000Block150Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part006] using hcert

def TailChunk000Sub000Block150Part007SupportExplicit : Finset ℕ :=
  ([6230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part007 : ℚ :=
  (47418908575 : ℚ) / 3109442510389248

def SurrogateDiagonalTailChunk000Sub000Block150Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6230
    = surrogateDiagTailX0RatChunk000Sub000Block150Part007

theorem surrogateDiagonalTailChunk000Sub000Block150Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part007] using hcert

def TailChunk000Sub000Block150Part008SupportExplicit : Finset ℕ :=
  ([6231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part008 : ℚ :=
  (61123469269 : ℚ) / 24596176107571200

def SurrogateDiagonalTailChunk000Sub000Block150Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6231
    = surrogateDiagTailX0RatChunk000Sub000Block150Part008

theorem surrogateDiagonalTailChunk000Sub000Block150Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part008] using hcert

def TailChunk000Sub000Block150Part009SupportExplicit : Finset ℕ :=
  ([6233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part009 : ℚ :=
  (3392515259 : ℚ) / 4611783020169600

def SurrogateDiagonalTailChunk000Sub000Block150Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6233
    = surrogateDiagTailX0RatChunk000Sub000Block150Part009

theorem surrogateDiagonalTailChunk000Sub000Block150Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part009] using hcert

def TailChunk000Sub000Block150Part010SupportExplicit : Finset ℕ :=
  ([6234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part010 : ℚ :=
  (741501966925 : ℚ) / 46444710010025088

def SurrogateDiagonalTailChunk000Sub000Block150Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6234
    = surrogateDiagTailX0RatChunk000Sub000Block150Part010

theorem surrogateDiagonalTailChunk000Sub000Block150Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part010] using hcert

def TailChunk000Sub000Block150Part011SupportExplicit : Finset ℕ :=
  ([6235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part011 : ℚ :=
  (215216779025 : ℚ) / 612161645151780864

def SurrogateDiagonalTailChunk000Sub000Block150Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6235
    = surrogateDiagTailX0RatChunk000Sub000Block150Part011

theorem surrogateDiagonalTailChunk000Sub000Block150Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part011] using hcert

def TailChunk000Sub000Block150Part012SupportExplicit : Finset ℕ :=
  ([6238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part012 : ℚ :=
  (152002515625 : ℚ) / 59084193389392722

def SurrogateDiagonalTailChunk000Sub000Block150Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6238
    = surrogateDiagTailX0RatChunk000Sub000Block150Part012

theorem surrogateDiagonalTailChunk000Sub000Block150Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part012] using hcert

def TailChunk000Sub000Block150Part013SupportExplicit : Finset ℕ :=
  ([6239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part013 : ℚ :=
  (60951825725 : ℚ) / 1470283675892711424

def SurrogateDiagonalTailChunk000Sub000Block150Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6239
    = surrogateDiagTailX0RatChunk000Sub000Block150Part013

theorem surrogateDiagonalTailChunk000Sub000Block150Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part013] using hcert

def TailChunk000Sub000Block150Part014SupportExplicit : Finset ℕ :=
  ([6242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part014 : ℚ :=
  (243516025 : ℚ) / 94777495068672

def SurrogateDiagonalTailChunk000Sub000Block150Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6242
    = surrogateDiagTailX0RatChunk000Sub000Block150Part014

theorem surrogateDiagonalTailChunk000Sub000Block150Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part014] using hcert

def TailChunk000Sub000Block150Part015SupportExplicit : Finset ℕ :=
  ([6243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part015 : ℚ :=
  (10826335139 : ℚ) / 14977184405913600

def SurrogateDiagonalTailChunk000Sub000Block150Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6243
    = surrogateDiagTailX0RatChunk000Sub000Block150Part015

theorem surrogateDiagonalTailChunk000Sub000Block150Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part015] using hcert

def TailChunk000Sub000Block150Part016SupportExplicit : Finset ℕ :=
  ([6245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part016 : ℚ :=
  (195196187675 : ℚ) / 776417239602561024

def SurrogateDiagonalTailChunk000Sub000Block150Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6245
    = surrogateDiagTailX0RatChunk000Sub000Block150Part016

theorem surrogateDiagonalTailChunk000Sub000Block150Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part016] using hcert

def TailChunk000Sub000Block150Part017SupportExplicit : Finset ℕ :=
  ([6247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block150Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6247
    = surrogateDiagTailX0RatChunk000Sub000Block150Part017

theorem surrogateDiagonalTailChunk000Sub000Block150Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part017] using hcert

def TailChunk000Sub000Block150Part018SupportExplicit : Finset ℕ :=
  ([6249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part018 : ℚ :=
  (271178524325 : ℚ) / 375871802452144704

def SurrogateDiagonalTailChunk000Sub000Block150Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6249
    = surrogateDiagTailX0RatChunk000Sub000Block150Part018

theorem surrogateDiagonalTailChunk000Sub000Block150Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part018] using hcert

def TailChunk000Sub000Block150Part019SupportExplicit : Finset ℕ :=
  ([6251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part019 : ℚ :=
  (1867656569575 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub000Block150Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6251
    = surrogateDiagTailX0RatChunk000Sub000Block150Part019

theorem surrogateDiagonalTailChunk000Sub000Block150Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part019] using hcert

def TailChunk000Sub000Block150Part020SupportExplicit : Finset ℕ :=
  ([6254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part020 : ℚ :=
  (1170717137425 : ℚ) / 206896053980448768

def SurrogateDiagonalTailChunk000Sub000Block150Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6254
    = surrogateDiagTailX0RatChunk000Sub000Block150Part020

theorem surrogateDiagonalTailChunk000Sub000Block150Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part020] using hcert

def TailChunk000Sub000Block150Part021SupportExplicit : Finset ℕ :=
  ([6257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part021 : ℚ :=
  (611719515625 : ℚ) / 957533170935078912

def SurrogateDiagonalTailChunk000Sub000Block150Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6257
    = surrogateDiagTailX0RatChunk000Sub000Block150Part021

theorem surrogateDiagonalTailChunk000Sub000Block150Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part021] using hcert

def TailChunk000Sub000Block150Part022SupportExplicit : Finset ℕ :=
  ([6258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part022 : ℚ :=
  (622615365925 : ℚ) / 24877040010559488

def SurrogateDiagonalTailChunk000Sub000Block150Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6258
    = surrogateDiagTailX0RatChunk000Sub000Block150Part022

theorem surrogateDiagonalTailChunk000Sub000Block150Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part022] using hcert

def TailChunk000Sub000Block150Part023SupportExplicit : Finset ℕ :=
  ([6259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part023 : ℚ :=
  (29083376229 : ℚ) / 34702354208358400

def SurrogateDiagonalTailChunk000Sub000Block150Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6259
    = surrogateDiagTailX0RatChunk000Sub000Block150Part023

theorem surrogateDiagonalTailChunk000Sub000Block150Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part023] using hcert

def TailChunk000Sub000Block150Part024SupportExplicit : Finset ℕ :=
  ([6261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block150Part024 : ℚ :=
  (340163426275 : ℚ) / 189384340782457632

def SurrogateDiagonalTailChunk000Sub000Block150Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6261
    = surrogateDiagTailX0RatChunk000Sub000Block150Part024

theorem surrogateDiagonalTailChunk000Sub000Block150Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block150Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block150Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block150Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block150Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block150Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block150Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block150HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block150Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block150Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block150Part000
    + surrogateDiagTailX0RatChunk000Sub000Block150Part001
    + surrogateDiagTailX0RatChunk000Sub000Block150Part002
    + surrogateDiagTailX0RatChunk000Sub000Block150Part003
    + surrogateDiagTailX0RatChunk000Sub000Block150Part004
    + surrogateDiagTailX0RatChunk000Sub000Block150Part005
    + surrogateDiagTailX0RatChunk000Sub000Block150Part006
    + surrogateDiagTailX0RatChunk000Sub000Block150Part007
    + surrogateDiagTailX0RatChunk000Sub000Block150Part008
    + surrogateDiagTailX0RatChunk000Sub000Block150Part009

def surrogateDiagonalTailChunk000Sub000Block150MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block150Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block150Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block150Part010
    + surrogateDiagTailX0RatChunk000Sub000Block150Part011
    + surrogateDiagTailX0RatChunk000Sub000Block150Part012
    + surrogateDiagTailX0RatChunk000Sub000Block150Part013
    + surrogateDiagTailX0RatChunk000Sub000Block150Part014
    + surrogateDiagTailX0RatChunk000Sub000Block150Part015
    + surrogateDiagTailX0RatChunk000Sub000Block150Part016
    + surrogateDiagTailX0RatChunk000Sub000Block150Part017
    + surrogateDiagTailX0RatChunk000Sub000Block150Part018
    + surrogateDiagTailX0RatChunk000Sub000Block150Part019

def surrogateDiagonalTailChunk000Sub000Block150TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block150Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block150Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block150Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block150Part020
    + surrogateDiagTailX0RatChunk000Sub000Block150Part021
    + surrogateDiagTailX0RatChunk000Sub000Block150Part022
    + surrogateDiagTailX0RatChunk000Sub000Block150Part023
    + surrogateDiagTailX0RatChunk000Sub000Block150Part024

def surrogateDiagonalTailChunk000Sub000Block150Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block150HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block150MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block150TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block150 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block150Part000
    + surrogateDiagTailX0RatChunk000Sub000Block150Part001
    + surrogateDiagTailX0RatChunk000Sub000Block150Part002
    + surrogateDiagTailX0RatChunk000Sub000Block150Part003
    + surrogateDiagTailX0RatChunk000Sub000Block150Part004
    + surrogateDiagTailX0RatChunk000Sub000Block150Part005
    + surrogateDiagTailX0RatChunk000Sub000Block150Part006
    + surrogateDiagTailX0RatChunk000Sub000Block150Part007
    + surrogateDiagTailX0RatChunk000Sub000Block150Part008
    + surrogateDiagTailX0RatChunk000Sub000Block150Part009
    + surrogateDiagTailX0RatChunk000Sub000Block150Part010
    + surrogateDiagTailX0RatChunk000Sub000Block150Part011
    + surrogateDiagTailX0RatChunk000Sub000Block150Part012
    + surrogateDiagTailX0RatChunk000Sub000Block150Part013
    + surrogateDiagTailX0RatChunk000Sub000Block150Part014
    + surrogateDiagTailX0RatChunk000Sub000Block150Part015
    + surrogateDiagTailX0RatChunk000Sub000Block150Part016
    + surrogateDiagTailX0RatChunk000Sub000Block150Part017
    + surrogateDiagTailX0RatChunk000Sub000Block150Part018
    + surrogateDiagTailX0RatChunk000Sub000Block150Part019
    + surrogateDiagTailX0RatChunk000Sub000Block150Part020
    + surrogateDiagTailX0RatChunk000Sub000Block150Part021
    + surrogateDiagTailX0RatChunk000Sub000Block150Part022
    + surrogateDiagTailX0RatChunk000Sub000Block150Part023
    + surrogateDiagTailX0RatChunk000Sub000Block150Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block150_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block150Head + surrogateDiagTailX0RatChunk000Sub000Block150Mid + surrogateDiagTailX0RatChunk000Sub000Block150Tail =
      surrogateDiagTailX0RatChunk000Sub000Block150 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block150Head surrogateDiagTailX0RatChunk000Sub000Block150Mid surrogateDiagTailX0RatChunk000Sub000Block150Tail surrogateDiagTailX0RatChunk000Sub000Block150
  ring

def SurrogateDiagonalTailChunk000Sub000Block150HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block150HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block150Head

def SurrogateDiagonalTailChunk000Sub000Block150MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block150MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block150Mid

def SurrogateDiagonalTailChunk000Sub000Block150TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block150TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block150Tail

theorem surrogateDiagonalTailChunk000Sub000Block150_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block150HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block150MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block150TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block150Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block150 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block150HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block150MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block150TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block150Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block150_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

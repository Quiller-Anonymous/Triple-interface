import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [153,154). -/

/- Block 153 covers tail-support indices [3825,3850) and q from 6341 to 6383. -/

def TailChunk000Sub000Block153Part000SupportExplicit : Finset ℕ :=
  ([6341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part000 : ℚ :=
  (2323350082375 : ℚ) / 3138185049258590208

def SurrogateDiagonalTailChunk000Sub000Block153Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6341
    = surrogateDiagTailX0RatChunk000Sub000Block153Part000

theorem surrogateDiagonalTailChunk000Sub000Block153Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part000] using hcert

def TailChunk000Sub000Block153Part001SupportExplicit : Finset ℕ :=
  ([6342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part001 : ℚ :=
  (4710278057 : ℚ) / 209993990400000

def SurrogateDiagonalTailChunk000Sub000Block153Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6342
    = surrogateDiagTailX0RatChunk000Sub000Block153Part001

theorem surrogateDiagonalTailChunk000Sub000Block153Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part001] using hcert

def TailChunk000Sub000Block153Part002SupportExplicit : Finset ℕ :=
  ([6343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part002 : ℚ :=
  (628650765625 : ℚ) / 1011280931423946162

def SurrogateDiagonalTailChunk000Sub000Block153Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6343
    = surrogateDiagTailX0RatChunk000Sub000Block153Part002

theorem surrogateDiagonalTailChunk000Sub000Block153Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part002] using hcert

def TailChunk000Sub000Block153Part003SupportExplicit : Finset ℕ :=
  ([6346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part003 : ℚ :=
  (1168303669075 : ℚ) / 199319244089482368

def SurrogateDiagonalTailChunk000Sub000Block153Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6346
    = surrogateDiagTailX0RatChunk000Sub000Block153Part003

theorem surrogateDiagonalTailChunk000Sub000Block153Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part003] using hcert

def TailChunk000Sub000Block153Part004SupportExplicit : Finset ℕ :=
  ([6347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part004 : ℚ :=
  (89721644623 : ℚ) / 110097329238835200

def SurrogateDiagonalTailChunk000Sub000Block153Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6347
    = surrogateDiagTailX0RatChunk000Sub000Block153Part004

theorem surrogateDiagonalTailChunk000Sub000Block153Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part004] using hcert

def TailChunk000Sub000Block153Part005SupportExplicit : Finset ℕ :=
  ([6349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part005 : ℚ :=
  (2054331461275 : ℚ) / 2183457038109844608

def SurrogateDiagonalTailChunk000Sub000Block153Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6349
    = surrogateDiagTailX0RatChunk000Sub000Block153Part005

theorem surrogateDiagonalTailChunk000Sub000Block153Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part005] using hcert

def TailChunk000Sub000Block153Part006SupportExplicit : Finset ℕ :=
  ([6351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part006 : ℚ :=
  (443077921975 : ℚ) / 220286406252036096

def SurrogateDiagonalTailChunk000Sub000Block153Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6351
    = surrogateDiagTailX0RatChunk000Sub000Block153Part006

theorem surrogateDiagonalTailChunk000Sub000Block153Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part006] using hcert

def TailChunk000Sub000Block153Part007SupportExplicit : Finset ℕ :=
  ([6353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part007 : ℚ :=
  (630634515625 : ℚ) / 1017674342415409152

def SurrogateDiagonalTailChunk000Sub000Block153Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6353
    = surrogateDiagTailX0RatChunk000Sub000Block153Part007

theorem surrogateDiagonalTailChunk000Sub000Block153Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part007] using hcert

def TailChunk000Sub000Block153Part008SupportExplicit : Finset ℕ :=
  ([6355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part008 : ℚ :=
  (11957679809 : ℚ) / 8849129472000000

def SurrogateDiagonalTailChunk000Sub000Block153Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6355
    = surrogateDiagTailX0RatChunk000Sub000Block153Part008

theorem surrogateDiagonalTailChunk000Sub000Block153Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part008] using hcert

def TailChunk000Sub000Block153Part009SupportExplicit : Finset ℕ :=
  ([6357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part009 : ℚ :=
  (1515132953875 : ℚ) / 571389011211091968

def SurrogateDiagonalTailChunk000Sub000Block153Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6357
    = surrogateDiagTailX0RatChunk000Sub000Block153Part009

theorem surrogateDiagonalTailChunk000Sub000Block153Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part009] using hcert

def TailChunk000Sub000Block153Part010SupportExplicit : Finset ℕ :=
  ([6359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part010 : ℚ :=
  (631826265625 : ℚ) / 1021524911066197362

def SurrogateDiagonalTailChunk000Sub000Block153Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6359
    = surrogateDiagTailX0RatChunk000Sub000Block153Part010

theorem surrogateDiagonalTailChunk000Sub000Block153Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part010] using hcert

def TailChunk000Sub000Block153Part011SupportExplicit : Finset ℕ :=
  ([6361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part011 : ℚ :=
  (1011558025 : ℚ) / 1636497374188032

def SurrogateDiagonalTailChunk000Sub000Block153Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6361
    = surrogateDiagTailX0RatChunk000Sub000Block153Part011

theorem surrogateDiagonalTailChunk000Sub000Block153Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part011] using hcert

def TailChunk000Sub000Block153Part012SupportExplicit : Finset ℕ :=
  ([6362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part012 : ℚ :=
  (252969025 : ℚ) / 102281085886752

def SurrogateDiagonalTailChunk000Sub000Block153Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6362
    = surrogateDiagTailX0RatChunk000Sub000Block153Part012

theorem surrogateDiagonalTailChunk000Sub000Block153Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part012] using hcert

def TailChunk000Sub000Block153Part013SupportExplicit : Finset ℕ :=
  ([6365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part013 : ℚ :=
  (887355065525 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub000Block153Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6365
    = surrogateDiagTailX0RatChunk000Sub000Block153Part013

theorem surrogateDiagonalTailChunk000Sub000Block153Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part013] using hcert

def TailChunk000Sub000Block153Part014SupportExplicit : Finset ℕ :=
  ([6366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part014 : ℚ :=
  (19691362237 : ℚ) / 2020367128627200

def SurrogateDiagonalTailChunk000Sub000Block153Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6366
    = surrogateDiagTailX0RatChunk000Sub000Block153Part014

theorem surrogateDiagonalTailChunk000Sub000Block153Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part014] using hcert

def TailChunk000Sub000Block153Part015SupportExplicit : Finset ℕ :=
  ([6367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part015 : ℚ :=
  (633417015625 : ℚ) / 1026675987709924242

def SurrogateDiagonalTailChunk000Sub000Block153Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6367
    = surrogateDiagTailX0RatChunk000Sub000Block153Part015

theorem surrogateDiagonalTailChunk000Sub000Block153Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part015] using hcert

def TailChunk000Sub000Block153Part016SupportExplicit : Finset ℕ :=
  ([6369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part016 : ℚ :=
  (50761096777 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub000Block153Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6369
    = surrogateDiagTailX0RatChunk000Sub000Block153Part016

theorem surrogateDiagonalTailChunk000Sub000Block153Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part016] using hcert

def TailChunk000Sub000Block153Part017SupportExplicit : Finset ℕ :=
  ([6371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part017 : ℚ :=
  (24167141725 : ℚ) / 34333550408374272

def SurrogateDiagonalTailChunk000Sub000Block153Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6371
    = surrogateDiagTailX0RatChunk000Sub000Block153Part017

theorem surrogateDiagonalTailChunk000Sub000Block153Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part017] using hcert

def TailChunk000Sub000Block153Part018SupportExplicit : Finset ℕ :=
  ([6373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part018 : ℚ :=
  (634611390625 : ℚ) / 1030552060750470432

def SurrogateDiagonalTailChunk000Sub000Block153Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6373
    = surrogateDiagTailX0RatChunk000Sub000Block153Part018

theorem surrogateDiagonalTailChunk000Sub000Block153Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part018] using hcert

def TailChunk000Sub000Block153Part019SupportExplicit : Finset ℕ :=
  ([6374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part019 : ℚ :=
  (1269367200775 : ℚ) / 257638015187617608

def SurrogateDiagonalTailChunk000Sub000Block153Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6374
    = surrogateDiagTailX0RatChunk000Sub000Block153Part019

theorem surrogateDiagonalTailChunk000Sub000Block153Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part019] using hcert

def TailChunk000Sub000Block153Part020SupportExplicit : Finset ℕ :=
  ([6377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part020 : ℚ :=
  (84971698327 : ℚ) / 88890924085891200

def SurrogateDiagonalTailChunk000Sub000Block153Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6377
    = surrogateDiagTailX0RatChunk000Sub000Block153Part020

theorem surrogateDiagonalTailChunk000Sub000Block153Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part020] using hcert

def TailChunk000Sub000Block153Part021SupportExplicit : Finset ℕ :=
  ([6378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part021 : ℚ :=
  (776158266325 : ℚ) / 50891459790146688

def SurrogateDiagonalTailChunk000Sub000Block153Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6378
    = surrogateDiagTailX0RatChunk000Sub000Block153Part021

theorem surrogateDiagonalTailChunk000Sub000Block153Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part021] using hcert

def TailChunk000Sub000Block153Part022SupportExplicit : Finset ℕ :=
  ([6379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part022 : ℚ :=
  (635806890625 : ℚ) / 1034439098628845682

def SurrogateDiagonalTailChunk000Sub000Block153Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6379
    = surrogateDiagTailX0RatChunk000Sub000Block153Part022

theorem surrogateDiagonalTailChunk000Sub000Block153Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part022] using hcert

def TailChunk000Sub000Block153Part023SupportExplicit : Finset ℕ :=
  ([6382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part023 : ℚ :=
  (50902222519 : ℚ) / 10357372181224200

def SurrogateDiagonalTailChunk000Sub000Block153Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6382
    = surrogateDiagTailX0RatChunk000Sub000Block153Part023

theorem surrogateDiagonalTailChunk000Sub000Block153Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part023] using hcert

def TailChunk000Sub000Block153Part024SupportExplicit : Finset ℕ :=
  ([6383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block153Part024 : ℚ :=
  (92005326121 : ℚ) / 119562821318707200

def SurrogateDiagonalTailChunk000Sub000Block153Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6383
    = surrogateDiagTailX0RatChunk000Sub000Block153Part024

theorem surrogateDiagonalTailChunk000Sub000Block153Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block153Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block153Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block153Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block153Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block153Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block153Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block153HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block153Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block153Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block153Part000
    + surrogateDiagTailX0RatChunk000Sub000Block153Part001
    + surrogateDiagTailX0RatChunk000Sub000Block153Part002
    + surrogateDiagTailX0RatChunk000Sub000Block153Part003
    + surrogateDiagTailX0RatChunk000Sub000Block153Part004
    + surrogateDiagTailX0RatChunk000Sub000Block153Part005
    + surrogateDiagTailX0RatChunk000Sub000Block153Part006
    + surrogateDiagTailX0RatChunk000Sub000Block153Part007
    + surrogateDiagTailX0RatChunk000Sub000Block153Part008
    + surrogateDiagTailX0RatChunk000Sub000Block153Part009

def surrogateDiagonalTailChunk000Sub000Block153MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block153Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block153Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block153Part010
    + surrogateDiagTailX0RatChunk000Sub000Block153Part011
    + surrogateDiagTailX0RatChunk000Sub000Block153Part012
    + surrogateDiagTailX0RatChunk000Sub000Block153Part013
    + surrogateDiagTailX0RatChunk000Sub000Block153Part014
    + surrogateDiagTailX0RatChunk000Sub000Block153Part015
    + surrogateDiagTailX0RatChunk000Sub000Block153Part016
    + surrogateDiagTailX0RatChunk000Sub000Block153Part017
    + surrogateDiagTailX0RatChunk000Sub000Block153Part018
    + surrogateDiagTailX0RatChunk000Sub000Block153Part019

def surrogateDiagonalTailChunk000Sub000Block153TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block153Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block153Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block153Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block153Part020
    + surrogateDiagTailX0RatChunk000Sub000Block153Part021
    + surrogateDiagTailX0RatChunk000Sub000Block153Part022
    + surrogateDiagTailX0RatChunk000Sub000Block153Part023
    + surrogateDiagTailX0RatChunk000Sub000Block153Part024

def surrogateDiagonalTailChunk000Sub000Block153Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block153HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block153MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block153TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block153 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block153Part000
    + surrogateDiagTailX0RatChunk000Sub000Block153Part001
    + surrogateDiagTailX0RatChunk000Sub000Block153Part002
    + surrogateDiagTailX0RatChunk000Sub000Block153Part003
    + surrogateDiagTailX0RatChunk000Sub000Block153Part004
    + surrogateDiagTailX0RatChunk000Sub000Block153Part005
    + surrogateDiagTailX0RatChunk000Sub000Block153Part006
    + surrogateDiagTailX0RatChunk000Sub000Block153Part007
    + surrogateDiagTailX0RatChunk000Sub000Block153Part008
    + surrogateDiagTailX0RatChunk000Sub000Block153Part009
    + surrogateDiagTailX0RatChunk000Sub000Block153Part010
    + surrogateDiagTailX0RatChunk000Sub000Block153Part011
    + surrogateDiagTailX0RatChunk000Sub000Block153Part012
    + surrogateDiagTailX0RatChunk000Sub000Block153Part013
    + surrogateDiagTailX0RatChunk000Sub000Block153Part014
    + surrogateDiagTailX0RatChunk000Sub000Block153Part015
    + surrogateDiagTailX0RatChunk000Sub000Block153Part016
    + surrogateDiagTailX0RatChunk000Sub000Block153Part017
    + surrogateDiagTailX0RatChunk000Sub000Block153Part018
    + surrogateDiagTailX0RatChunk000Sub000Block153Part019
    + surrogateDiagTailX0RatChunk000Sub000Block153Part020
    + surrogateDiagTailX0RatChunk000Sub000Block153Part021
    + surrogateDiagTailX0RatChunk000Sub000Block153Part022
    + surrogateDiagTailX0RatChunk000Sub000Block153Part023
    + surrogateDiagTailX0RatChunk000Sub000Block153Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block153_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block153Head + surrogateDiagTailX0RatChunk000Sub000Block153Mid + surrogateDiagTailX0RatChunk000Sub000Block153Tail =
      surrogateDiagTailX0RatChunk000Sub000Block153 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block153Head surrogateDiagTailX0RatChunk000Sub000Block153Mid surrogateDiagTailX0RatChunk000Sub000Block153Tail surrogateDiagTailX0RatChunk000Sub000Block153
  ring

def SurrogateDiagonalTailChunk000Sub000Block153HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block153HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block153Head

def SurrogateDiagonalTailChunk000Sub000Block153MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block153MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block153Mid

def SurrogateDiagonalTailChunk000Sub000Block153TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block153TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block153Tail

theorem surrogateDiagonalTailChunk000Sub000Block153_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block153HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block153MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block153TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block153Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block153 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block153HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block153MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block153TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block153Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block153_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

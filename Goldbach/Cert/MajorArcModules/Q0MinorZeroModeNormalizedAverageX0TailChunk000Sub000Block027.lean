import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [27,28). -/

/- Block 027 covers tail-support indices [675,700) and q from 1162 to 1201. -/

def TailChunk000Sub000Block027Part000SupportExplicit : Finset ℕ :=
  ([1162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part000 : ℚ :=
  (8859769175 : ℚ) / 8139819318336

def SurrogateDiagonalTailChunk000Sub000Block027Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1162
    = surrogateDiagTailX0RatChunk000Sub000Block027Part000

theorem surrogateDiagonalTailChunk000Sub000Block027Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part000] using hcert

def TailChunk000Sub000Block027Part001SupportExplicit : Finset ℕ :=
  ([1163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part001 : ℚ :=
  (211169835125 : ℚ) / 2279404364134884

def SurrogateDiagonalTailChunk000Sub000Block027Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1163
    = surrogateDiagTailX0RatChunk000Sub000Block027Part001

theorem surrogateDiagonalTailChunk000Sub000Block027Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part001] using hcert

def TailChunk000Sub000Block027Part002SupportExplicit : Finset ℕ :=
  ([1165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part002 : ℚ :=
  (277146532525 : ℚ) / 1854465523580928

def SurrogateDiagonalTailChunk000Sub000Block027Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1165
    = surrogateDiagTailX0RatChunk000Sub000Block027Part002

theorem surrogateDiagonalTailChunk000Sub000Block027Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part002] using hcert

def TailChunk000Sub000Block027Part003SupportExplicit : Finset ℕ :=
  ([1166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part003 : ℚ :=
  (678934597 : ℚ) / 731307832320

def SurrogateDiagonalTailChunk000Sub000Block027Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1166
    = surrogateDiagTailX0RatChunk000Sub000Block027Part003

theorem surrogateDiagonalTailChunk000Sub000Block027Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part003] using hcert

def TailChunk000Sub000Block027Part004SupportExplicit : Finset ℕ :=
  ([1167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part004 : ℚ :=
  (58973460175 : ℚ) / 226680286351872

def SurrogateDiagonalTailChunk000Sub000Block027Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1167
    = surrogateDiagTailX0RatChunk000Sub000Block027Part004

theorem surrogateDiagonalTailChunk000Sub000Block027Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part004] using hcert

def TailChunk000Sub000Block027Part005SupportExplicit : Finset ℕ :=
  ([1169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part005 : ℚ :=
  (292982373625 : ℚ) / 2460731408512128

def SurrogateDiagonalTailChunk000Sub000Block027Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1169
    = surrogateDiagTailX0RatChunk000Sub000Block027Part005

theorem surrogateDiagonalTailChunk000Sub000Block027Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part005] using hcert

def TailChunk000Sub000Block027Part006SupportExplicit : Finset ℕ :=
  ([1171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part006 : ℚ :=
  (1712680009 : ℚ) / 18742619874420

def SurrogateDiagonalTailChunk000Sub000Block027Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1171
    = surrogateDiagTailX0RatChunk000Sub000Block027Part006

theorem surrogateDiagonalTailChunk000Sub000Block027Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part006] using hcert

def TailChunk000Sub000Block027Part007SupportExplicit : Finset ℕ :=
  ([1173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part007 : ℚ :=
  (215554284775 : ℚ) / 614210866249728

def SurrogateDiagonalTailChunk000Sub000Block027Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1173
    = surrogateDiagTailX0RatChunk000Sub000Block027Part007

theorem surrogateDiagonalTailChunk000Sub000Block027Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part007] using hcert

def TailChunk000Sub000Block027Part008SupportExplicit : Finset ℕ :=
  ([1174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part008 : ℚ :=
  (8062914600 : ℚ) / 12285874685267

def SurrogateDiagonalTailChunk000Sub000Block027Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1174
    = surrogateDiagTailX0RatChunk000Sub000Block027Part008

theorem surrogateDiagonalTailChunk000Sub000Block027Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part008] using hcert

def TailChunk000Sub000Block027Part009SupportExplicit : Finset ℕ :=
  ([1177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part009 : ℚ :=
  (1279270563 : ℚ) / 10522745461600

def SurrogateDiagonalTailChunk000Sub000Block027Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1177
    = surrogateDiagTailX0RatChunk000Sub000Block027Part009

theorem surrogateDiagonalTailChunk000Sub000Block027Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part009] using hcert

def TailChunk000Sub000Block027Part010SupportExplicit : Finset ℕ :=
  ([1178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part010 : ℚ :=
  (7121579743 : ℚ) / 8504756611200

def SurrogateDiagonalTailChunk000Sub000Block027Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1178
    = surrogateDiagTailX0RatChunk000Sub000Block027Part010

theorem surrogateDiagonalTailChunk000Sub000Block027Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part010] using hcert

def TailChunk000Sub000Block027Part011SupportExplicit : Finset ℕ :=
  ([1181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part011 : ℚ :=
  (6969620717 : ℚ) / 96958275777600

def SurrogateDiagonalTailChunk000Sub000Block027Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1181
    = surrogateDiagTailX0RatChunk000Sub000Block027Part011

theorem surrogateDiagonalTailChunk000Sub000Block027Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part011] using hcert

def TailChunk000Sub000Block027Part012SupportExplicit : Finset ℕ :=
  ([1182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part012 : ℚ :=
  (7393389475 : ℚ) / 3690210534528

def SurrogateDiagonalTailChunk000Sub000Block027Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1182
    = surrogateDiagTailX0RatChunk000Sub000Block027Part012

theorem surrogateDiagonalTailChunk000Sub000Block027Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part012] using hcert

def TailChunk000Sub000Block027Part013SupportExplicit : Finset ℕ :=
  ([1185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part013 : ℚ :=
  (52529129125 : ℚ) / 94777495068672

def SurrogateDiagonalTailChunk000Sub000Block027Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1185
    = surrogateDiagTailX0RatChunk000Sub000Block027Part013

theorem surrogateDiagonalTailChunk000Sub000Block027Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part013] using hcert

def TailChunk000Sub000Block027Part014SupportExplicit : Finset ℕ :=
  ([1186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part014 : ℚ :=
  (43894586425 : ℚ) / 76780987686912

def SurrogateDiagonalTailChunk000Sub000Block027Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1186
    = surrogateDiagTailX0RatChunk000Sub000Block027Part014

theorem surrogateDiagonalTailChunk000Sub000Block027Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part014] using hcert

def TailChunk000Sub000Block027Part015SupportExplicit : Finset ℕ :=
  ([1187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part015 : ℚ :=
  (176015452325 : ℚ) / 2473635012096804

def SurrogateDiagonalTailChunk000Sub000Block027Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1187
    = surrogateDiagTailX0RatChunk000Sub000Block027Part015

theorem surrogateDiagonalTailChunk000Sub000Block027Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part015] using hcert

def TailChunk000Sub000Block027Part016SupportExplicit : Finset ℕ :=
  ([1189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part016 : ℚ :=
  (13359701767 : ℚ) / 157383406387200

def SurrogateDiagonalTailChunk000Sub000Block027Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1189
    = surrogateDiagTailX0RatChunk000Sub000Block027Part016

theorem surrogateDiagonalTailChunk000Sub000Block027Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part016] using hcert

def TailChunk000Sub000Block027Part017SupportExplicit : Finset ℕ :=
  ([1190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part017 : ℚ :=
  (6482416675 : ℚ) / 3020502859776

def SurrogateDiagonalTailChunk000Sub000Block027Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1190
    = surrogateDiagTailX0RatChunk000Sub000Block027Part017

theorem surrogateDiagonalTailChunk000Sub000Block027Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part017] using hcert

def TailChunk000Sub000Block027Part018SupportExplicit : Finset ℕ :=
  ([1191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part018 : ℚ :=
  (275098504825 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block027Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1191
    = surrogateDiagTailX0RatChunk000Sub000Block027Part018

theorem surrogateDiagonalTailChunk000Sub000Block027Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part018] using hcert

def TailChunk000Sub000Block027Part019SupportExplicit : Finset ℕ :=
  ([1193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part019 : ℚ :=
  (177799381325 : ℚ) / 2524072846746624

def SurrogateDiagonalTailChunk000Sub000Block027Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1193
    = surrogateDiagTailX0RatChunk000Sub000Block027Part019

theorem surrogateDiagonalTailChunk000Sub000Block027Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part019] using hcert

def TailChunk000Sub000Block027Part020SupportExplicit : Finset ℕ :=
  ([1194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part020 : ℚ :=
  (60353977175 : ℚ) / 30745220134464

def SurrogateDiagonalTailChunk000Sub000Block027Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1194
    = surrogateDiagTailX0RatChunk000Sub000Block027Part020

theorem surrogateDiagonalTailChunk000Sub000Block027Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part020] using hcert

def TailChunk000Sub000Block027Part021SupportExplicit : Finset ℕ :=
  ([1195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part021 : ℚ :=
  (35565361625 : ℚ) / 256734755563776

def SurrogateDiagonalTailChunk000Sub000Block027Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1195
    = surrogateDiagTailX0RatChunk000Sub000Block027Part021

theorem surrogateDiagonalTailChunk000Sub000Block027Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part021] using hcert

def TailChunk000Sub000Block027Part022SupportExplicit : Finset ℕ :=
  ([1198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part022 : ℚ :=
  (645841800 : ℚ) / 1024889398559

def SurrogateDiagonalTailChunk000Sub000Block027Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1198
    = surrogateDiagTailX0RatChunk000Sub000Block027Part022

theorem surrogateDiagonalTailChunk000Sub000Block027Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part022] using hcert

def TailChunk000Sub000Block027Part023SupportExplicit : Finset ℕ :=
  ([1199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part023 : ℚ :=
  (33894031 : ℚ) / 354364858800

def SurrogateDiagonalTailChunk000Sub000Block027Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1199
    = surrogateDiagTailX0RatChunk000Sub000Block027Part023

theorem surrogateDiagonalTailChunk000Sub000Block027Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part023] using hcert

def TailChunk000Sub000Block027Part024SupportExplicit : Finset ℕ :=
  ([1201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block027Part024 : ℚ :=
  (7207677797 : ℚ) / 103700736000000

def SurrogateDiagonalTailChunk000Sub000Block027Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1201
    = surrogateDiagTailX0RatChunk000Sub000Block027Part024

theorem surrogateDiagonalTailChunk000Sub000Block027Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block027Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block027Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block027Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block027Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block027Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block027HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block027Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block027Part000
    + surrogateDiagTailX0RatChunk000Sub000Block027Part001
    + surrogateDiagTailX0RatChunk000Sub000Block027Part002
    + surrogateDiagTailX0RatChunk000Sub000Block027Part003
    + surrogateDiagTailX0RatChunk000Sub000Block027Part004
    + surrogateDiagTailX0RatChunk000Sub000Block027Part005
    + surrogateDiagTailX0RatChunk000Sub000Block027Part006
    + surrogateDiagTailX0RatChunk000Sub000Block027Part007
    + surrogateDiagTailX0RatChunk000Sub000Block027Part008
    + surrogateDiagTailX0RatChunk000Sub000Block027Part009

def surrogateDiagonalTailChunk000Sub000Block027MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block027Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block027Part010
    + surrogateDiagTailX0RatChunk000Sub000Block027Part011
    + surrogateDiagTailX0RatChunk000Sub000Block027Part012
    + surrogateDiagTailX0RatChunk000Sub000Block027Part013
    + surrogateDiagTailX0RatChunk000Sub000Block027Part014
    + surrogateDiagTailX0RatChunk000Sub000Block027Part015
    + surrogateDiagTailX0RatChunk000Sub000Block027Part016
    + surrogateDiagTailX0RatChunk000Sub000Block027Part017
    + surrogateDiagTailX0RatChunk000Sub000Block027Part018
    + surrogateDiagTailX0RatChunk000Sub000Block027Part019

def surrogateDiagonalTailChunk000Sub000Block027TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block027Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block027Part020
    + surrogateDiagTailX0RatChunk000Sub000Block027Part021
    + surrogateDiagTailX0RatChunk000Sub000Block027Part022
    + surrogateDiagTailX0RatChunk000Sub000Block027Part023
    + surrogateDiagTailX0RatChunk000Sub000Block027Part024

def surrogateDiagonalTailChunk000Sub000Block027Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block027HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block027MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block027TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block027 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block027Part000
    + surrogateDiagTailX0RatChunk000Sub000Block027Part001
    + surrogateDiagTailX0RatChunk000Sub000Block027Part002
    + surrogateDiagTailX0RatChunk000Sub000Block027Part003
    + surrogateDiagTailX0RatChunk000Sub000Block027Part004
    + surrogateDiagTailX0RatChunk000Sub000Block027Part005
    + surrogateDiagTailX0RatChunk000Sub000Block027Part006
    + surrogateDiagTailX0RatChunk000Sub000Block027Part007
    + surrogateDiagTailX0RatChunk000Sub000Block027Part008
    + surrogateDiagTailX0RatChunk000Sub000Block027Part009
    + surrogateDiagTailX0RatChunk000Sub000Block027Part010
    + surrogateDiagTailX0RatChunk000Sub000Block027Part011
    + surrogateDiagTailX0RatChunk000Sub000Block027Part012
    + surrogateDiagTailX0RatChunk000Sub000Block027Part013
    + surrogateDiagTailX0RatChunk000Sub000Block027Part014
    + surrogateDiagTailX0RatChunk000Sub000Block027Part015
    + surrogateDiagTailX0RatChunk000Sub000Block027Part016
    + surrogateDiagTailX0RatChunk000Sub000Block027Part017
    + surrogateDiagTailX0RatChunk000Sub000Block027Part018
    + surrogateDiagTailX0RatChunk000Sub000Block027Part019
    + surrogateDiagTailX0RatChunk000Sub000Block027Part020
    + surrogateDiagTailX0RatChunk000Sub000Block027Part021
    + surrogateDiagTailX0RatChunk000Sub000Block027Part022
    + surrogateDiagTailX0RatChunk000Sub000Block027Part023
    + surrogateDiagTailX0RatChunk000Sub000Block027Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block027_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block027Head + surrogateDiagTailX0RatChunk000Sub000Block027Mid + surrogateDiagTailX0RatChunk000Sub000Block027Tail =
      surrogateDiagTailX0RatChunk000Sub000Block027 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block027Head surrogateDiagTailX0RatChunk000Sub000Block027Mid surrogateDiagTailX0RatChunk000Sub000Block027Tail surrogateDiagTailX0RatChunk000Sub000Block027
  ring

def SurrogateDiagonalTailChunk000Sub000Block027HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block027HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block027Head

def SurrogateDiagonalTailChunk000Sub000Block027MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block027MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block027Mid

def SurrogateDiagonalTailChunk000Sub000Block027TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block027TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block027Tail

theorem surrogateDiagonalTailChunk000Sub000Block027_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block027HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block027MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block027TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block027Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block027 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block027HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block027MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block027TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block027Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block027_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

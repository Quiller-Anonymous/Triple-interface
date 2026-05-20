import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [187,188). -/

/-- Block 187 covers tail-support indices [4675,4700) and q from 7737 to 7778. -/

def TailChunk000Sub000Block187Part000SupportExplicit : Finset ℕ :=
  ([7737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part000 : ℚ :=
  (32466537925 : ℚ) / 27612041638476882

def SurrogateDiagonalTailChunk000Sub000Block187Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7737
    = surrogateDiagTailX0RatChunk000Sub000Block187Part000

theorem surrogateDiagonalTailChunk000Sub000Block187Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part000] using hcert

def TailChunk000Sub000Block187Part001SupportExplicit : Finset ℕ :=
  ([7738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part001 : ℚ :=
  (914159302975 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub000Block187Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7738
    = surrogateDiagTailX0RatChunk000Sub000Block187Part001

theorem surrogateDiagonalTailChunk000Sub000Block187Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part001] using hcert

def TailChunk000Sub000Block187Part002SupportExplicit : Finset ℕ :=
  ([7739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part002 : ℚ :=
  (4145110799 : ℚ) / 9334820856453120

def SurrogateDiagonalTailChunk000Sub000Block187Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7739
    = surrogateDiagTailX0RatChunk000Sub000Block187Part002

theorem surrogateDiagonalTailChunk000Sub000Block187Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part002] using hcert

def TailChunk000Sub000Block187Part003SupportExplicit : Finset ℕ :=
  ([7741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part003 : ℚ :=
  (1498077025 : ℚ) / 3589638321867552

def SurrogateDiagonalTailChunk000Sub000Block187Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7741
    = surrogateDiagTailX0RatChunk000Sub000Block187Part003

theorem surrogateDiagonalTailChunk000Sub000Block187Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part003] using hcert

def TailChunk000Sub000Block187Part004SupportExplicit : Finset ℕ :=
  ([7743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part004 : ℚ :=
  (655834387575 : ℚ) / 491573429955198976

def SurrogateDiagonalTailChunk000Sub000Block187Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7743
    = surrogateDiagTailX0RatChunk000Sub000Block187Part004

theorem surrogateDiagonalTailChunk000Sub000Block187Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part004] using hcert

def TailChunk000Sub000Block187Part005SupportExplicit : Finset ℕ :=
  ([7745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part005 : ℚ :=
  (474566724475 : ℚ) / 612631606932062208

def SurrogateDiagonalTailChunk000Sub000Block187Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7745
    = surrogateDiagTailX0RatChunk000Sub000Block187Part005

theorem surrogateDiagonalTailChunk000Sub000Block187Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part005] using hcert

def TailChunk000Sub000Block187Part006SupportExplicit : Finset ℕ :=
  ([7746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part006 : ℚ :=
  (29151733507 : ℚ) / 4431652249219200

def SurrogateDiagonalTailChunk000Sub000Block187Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7746
    = surrogateDiagTailX0RatChunk000Sub000Block187Part006

theorem surrogateDiagonalTailChunk000Sub000Block187Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part006] using hcert

def TailChunk000Sub000Block187Part007SupportExplicit : Finset ℕ :=
  ([7747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part007 : ℚ :=
  (403218191 : ℚ) / 907552027710720

def SurrogateDiagonalTailChunk000Sub000Block187Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7747
    = surrogateDiagTailX0RatChunk000Sub000Block187Part007

theorem surrogateDiagonalTailChunk000Sub000Block187Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part007] using hcert

def TailChunk000Sub000Block187Part008SupportExplicit : Finset ℕ :=
  ([7751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part008 : ℚ :=
  (391259193175 : ℚ) / 829530163049398272

def SurrogateDiagonalTailChunk000Sub000Block187Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7751
    = surrogateDiagTailX0RatChunk000Sub000Block187Part008

theorem surrogateDiagonalTailChunk000Sub000Block187Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part008] using hcert

def TailChunk000Sub000Block187Part009SupportExplicit : Finset ℕ :=
  ([7753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part009 : ℚ :=
  (939203265625 : ℚ) / 2257469668026634752

def SurrogateDiagonalTailChunk000Sub000Block187Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7753
    = surrogateDiagTailX0RatChunk000Sub000Block187Part009

theorem surrogateDiagonalTailChunk000Sub000Block187Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part009] using hcert

def TailChunk000Sub000Block187Part010SupportExplicit : Finset ℕ :=
  ([7754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part010 : ℚ :=
  (1878515346775 : ℚ) / 564367417006658688

def SurrogateDiagonalTailChunk000Sub000Block187Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7754
    = surrogateDiagTailX0RatChunk000Sub000Block187Part010

theorem surrogateDiagonalTailChunk000Sub000Block187Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part010] using hcert

def TailChunk000Sub000Block187Part011SupportExplicit : Finset ℕ :=
  ([7755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part011 : ℚ :=
  (5413370083 : ℚ) / 1834332770795520

def SurrogateDiagonalTailChunk000Sub000Block187Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7755
    = surrogateDiagTailX0RatChunk000Sub000Block187Part011

theorem surrogateDiagonalTailChunk000Sub000Block187Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part011] using hcert

def TailChunk000Sub000Block187Part012SupportExplicit : Finset ℕ :=
  ([7757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part012 : ℚ :=
  (940172640625 : ℚ) / 2262132655718490912

def SurrogateDiagonalTailChunk000Sub000Block187Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7757
    = surrogateDiagTailX0RatChunk000Sub000Block187Part012

theorem surrogateDiagonalTailChunk000Sub000Block187Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part012] using hcert

def TailChunk000Sub000Block187Part013SupportExplicit : Finset ℕ :=
  ([7759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part013 : ℚ :=
  (940657515625 : ℚ) / 2264466856639575762

def SurrogateDiagonalTailChunk000Sub000Block187Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7759
    = surrogateDiagTailX0RatChunk000Sub000Block187Part013

theorem surrogateDiagonalTailChunk000Sub000Block187Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part013] using hcert

def TailChunk000Sub000Block187Part014SupportExplicit : Finset ℕ :=
  ([7761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part014 : ℚ :=
  (3867735125 : ℚ) / 2623592118140928

def SurrogateDiagonalTailChunk000Sub000Block187Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7761
    = surrogateDiagTailX0RatChunk000Sub000Block187Part014

theorem surrogateDiagonalTailChunk000Sub000Block187Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part014] using hcert

def TailChunk000Sub000Block187Part015SupportExplicit : Finset ℕ :=
  ([7762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part015 : ℚ :=
  (75295742839 : ℚ) / 22668028635187200

def SurrogateDiagonalTailChunk000Sub000Block187Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7762
    = surrogateDiagTailX0RatChunk000Sub000Block187Part015

theorem surrogateDiagonalTailChunk000Sub000Block187Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part015] using hcert

def TailChunk000Sub000Block187Part016SupportExplicit : Finset ℕ :=
  ([7763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part016 : ℚ :=
  (3071584483375 : ℚ) / 4884171464908228608

def SurrogateDiagonalTailChunk000Sub000Block187Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7763
    = surrogateDiagTailX0RatChunk000Sub000Block187Part016

theorem surrogateDiagonalTailChunk000Sub000Block187Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part016] using hcert

def TailChunk000Sub000Block187Part017SupportExplicit : Finset ℕ :=
  ([7765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part017 : ℚ :=
  (1431064068575 : ℚ) / 1856964905794535424

def SurrogateDiagonalTailChunk000Sub000Block187Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7765
    = surrogateDiagTailX0RatChunk000Sub000Block187Part017

theorem surrogateDiagonalTailChunk000Sub000Block187Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part017] using hcert

def TailChunk000Sub000Block187Part018SupportExplicit : Finset ℕ :=
  ([7766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part018 : ℚ :=
  (21934295847 : ℚ) / 5118423885414400

def SurrogateDiagonalTailChunk000Sub000Block187Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7766
    = surrogateDiagTailX0RatChunk000Sub000Block187Part018

theorem surrogateDiagonalTailChunk000Sub000Block187Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part018] using hcert

def TailChunk000Sub000Block187Part019SupportExplicit : Finset ℕ :=
  ([7769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part019 : ℚ :=
  (144271489925 : ℚ) / 295226214891651072

def SurrogateDiagonalTailChunk000Sub000Block187Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7769
    = surrogateDiagTailX0RatChunk000Sub000Block187Part019

theorem surrogateDiagonalTailChunk000Sub000Block187Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part019] using hcert

def TailChunk000Sub000Block187Part020SupportExplicit : Finset ℕ :=
  ([7770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part020 : ℚ :=
  (115578155425 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub000Block187Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7770
    = surrogateDiagTailX0RatChunk000Sub000Block187Part020

theorem surrogateDiagonalTailChunk000Sub000Block187Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part020] using hcert

def TailChunk000Sub000Block187Part021SupportExplicit : Finset ℕ :=
  ([7771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part021 : ℚ :=
  (130194603625 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub000Block187Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7771
    = surrogateDiagTailX0RatChunk000Sub000Block187Part021

theorem surrogateDiagonalTailChunk000Sub000Block187Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part021] using hcert

def TailChunk000Sub000Block187Part022SupportExplicit : Finset ℕ :=
  ([7773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part022 : ℚ :=
  (16779393269 : ℚ) / 36006084264897600

def SurrogateDiagonalTailChunk000Sub000Block187Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7773
    = surrogateDiagTailX0RatChunk000Sub000Block187Part022

theorem surrogateDiagonalTailChunk000Sub000Block187Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part022] using hcert

def TailChunk000Sub000Block187Part023SupportExplicit : Finset ℕ :=
  ([7777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part023 : ℚ :=
  (18018085927 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub000Block187Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7777
    = surrogateDiagTailX0RatChunk000Sub000Block187Part023

theorem surrogateDiagonalTailChunk000Sub000Block187Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part023] using hcert

def TailChunk000Sub000Block187Part024SupportExplicit : Finset ℕ :=
  ([7778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part024 : ℚ :=
  (236317515625 : ℚ) / 142847252802772992

def SurrogateDiagonalTailChunk000Sub000Block187Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7778
    = surrogateDiagTailX0RatChunk000Sub000Block187Part024

theorem surrogateDiagonalTailChunk000Sub000Block187Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block187HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block187Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part000
    + surrogateDiagTailX0RatChunk000Sub000Block187Part001
    + surrogateDiagTailX0RatChunk000Sub000Block187Part002
    + surrogateDiagTailX0RatChunk000Sub000Block187Part003
    + surrogateDiagTailX0RatChunk000Sub000Block187Part004
    + surrogateDiagTailX0RatChunk000Sub000Block187Part005
    + surrogateDiagTailX0RatChunk000Sub000Block187Part006
    + surrogateDiagTailX0RatChunk000Sub000Block187Part007
    + surrogateDiagTailX0RatChunk000Sub000Block187Part008
    + surrogateDiagTailX0RatChunk000Sub000Block187Part009

def surrogateDiagonalTailChunk000Sub000Block187MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block187Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part010
    + surrogateDiagTailX0RatChunk000Sub000Block187Part011
    + surrogateDiagTailX0RatChunk000Sub000Block187Part012
    + surrogateDiagTailX0RatChunk000Sub000Block187Part013
    + surrogateDiagTailX0RatChunk000Sub000Block187Part014
    + surrogateDiagTailX0RatChunk000Sub000Block187Part015
    + surrogateDiagTailX0RatChunk000Sub000Block187Part016
    + surrogateDiagTailX0RatChunk000Sub000Block187Part017
    + surrogateDiagTailX0RatChunk000Sub000Block187Part018
    + surrogateDiagTailX0RatChunk000Sub000Block187Part019

def surrogateDiagonalTailChunk000Sub000Block187TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block187Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part020
    + surrogateDiagTailX0RatChunk000Sub000Block187Part021
    + surrogateDiagTailX0RatChunk000Sub000Block187Part022
    + surrogateDiagTailX0RatChunk000Sub000Block187Part023
    + surrogateDiagTailX0RatChunk000Sub000Block187Part024

def surrogateDiagonalTailChunk000Sub000Block187Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block187HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block187MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block187TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block187 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part000
    + surrogateDiagTailX0RatChunk000Sub000Block187Part001
    + surrogateDiagTailX0RatChunk000Sub000Block187Part002
    + surrogateDiagTailX0RatChunk000Sub000Block187Part003
    + surrogateDiagTailX0RatChunk000Sub000Block187Part004
    + surrogateDiagTailX0RatChunk000Sub000Block187Part005
    + surrogateDiagTailX0RatChunk000Sub000Block187Part006
    + surrogateDiagTailX0RatChunk000Sub000Block187Part007
    + surrogateDiagTailX0RatChunk000Sub000Block187Part008
    + surrogateDiagTailX0RatChunk000Sub000Block187Part009
    + surrogateDiagTailX0RatChunk000Sub000Block187Part010
    + surrogateDiagTailX0RatChunk000Sub000Block187Part011
    + surrogateDiagTailX0RatChunk000Sub000Block187Part012
    + surrogateDiagTailX0RatChunk000Sub000Block187Part013
    + surrogateDiagTailX0RatChunk000Sub000Block187Part014
    + surrogateDiagTailX0RatChunk000Sub000Block187Part015
    + surrogateDiagTailX0RatChunk000Sub000Block187Part016
    + surrogateDiagTailX0RatChunk000Sub000Block187Part017
    + surrogateDiagTailX0RatChunk000Sub000Block187Part018
    + surrogateDiagTailX0RatChunk000Sub000Block187Part019
    + surrogateDiagTailX0RatChunk000Sub000Block187Part020
    + surrogateDiagTailX0RatChunk000Sub000Block187Part021
    + surrogateDiagTailX0RatChunk000Sub000Block187Part022
    + surrogateDiagTailX0RatChunk000Sub000Block187Part023
    + surrogateDiagTailX0RatChunk000Sub000Block187Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block187_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block187Head + surrogateDiagTailX0RatChunk000Sub000Block187Mid + surrogateDiagTailX0RatChunk000Sub000Block187Tail =
      surrogateDiagTailX0RatChunk000Sub000Block187 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block187Head surrogateDiagTailX0RatChunk000Sub000Block187Mid surrogateDiagTailX0RatChunk000Sub000Block187Tail surrogateDiagTailX0RatChunk000Sub000Block187
  ring

def SurrogateDiagonalTailChunk000Sub000Block187HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block187HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block187Head

def SurrogateDiagonalTailChunk000Sub000Block187MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block187MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block187Mid

def SurrogateDiagonalTailChunk000Sub000Block187TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block187TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block187Tail

theorem surrogateDiagonalTailChunk000Sub000Block187_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block187HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block187MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block187TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block187Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block187 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block187HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block187MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block187TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block187Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block187_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

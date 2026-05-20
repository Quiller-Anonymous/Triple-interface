import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block012
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block013
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block014
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block016
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block017
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block018
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Block019

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk000Sub001First100Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block000Sum X0
    + surrogateDiagonalTailChunk000Sub001Block001Sum X0
    + surrogateDiagonalTailChunk000Sub001Block002Sum X0
    + surrogateDiagonalTailChunk000Sub001Block003Sum X0

def surrogateDiagTailX0RatChunk000Sub001First100 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block000
    + surrogateDiagTailX0RatChunk000Sub001Block001
    + surrogateDiagTailX0RatChunk000Sub001Block002
    + surrogateDiagTailX0RatChunk000Sub001Block003

theorem surrogateDiagTailX0RatChunk000Sub001First100_eq_blocks :
    surrogateDiagTailX0RatChunk000Sub001Block000
      + surrogateDiagTailX0RatChunk000Sub001Block001
      + surrogateDiagTailX0RatChunk000Sub001Block002
      + surrogateDiagTailX0RatChunk000Sub001Block003
      = surrogateDiagTailX0RatChunk000Sub001First100 := by
  unfold surrogateDiagTailX0RatChunk000Sub001First100
  ring

def SurrogateDiagonalTailChunk000Sub001First100CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001First100Sum X0 = surrogateDiagTailX0RatChunk000Sub001First100

def SurrogateDiagonalTailChunk000Sub001Block000CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block000Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block000
def SurrogateDiagonalTailChunk000Sub001Block001CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block001Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block001
def SurrogateDiagonalTailChunk000Sub001Block002CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block002Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block002
def SurrogateDiagonalTailChunk000Sub001Block003CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block003Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block003

theorem surrogateDiagonalTailChunk000Sub001First100_eq_cert_explicit
    (hBlock000 : SurrogateDiagonalTailChunk000Sub001Block000CertificateAt X0)
    (hBlock001 : SurrogateDiagonalTailChunk000Sub001Block001CertificateAt X0)
    (hBlock002 : SurrogateDiagonalTailChunk000Sub001Block002CertificateAt X0)
    (hBlock003 : SurrogateDiagonalTailChunk000Sub001Block003CertificateAt X0)
    : surrogateDiagonalTailChunk000Sub001First100Sum X0 = surrogateDiagTailX0RatChunk000Sub001First100 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block000CertificateAt at hBlock000
  unfold SurrogateDiagonalTailChunk000Sub001Block001CertificateAt at hBlock001
  unfold SurrogateDiagonalTailChunk000Sub001Block002CertificateAt at hBlock002
  unfold SurrogateDiagonalTailChunk000Sub001Block003CertificateAt at hBlock003
  unfold surrogateDiagonalTailChunk000Sub001First100Sum
  rw [hBlock000, hBlock001, hBlock002, hBlock003]
  exact surrogateDiagTailX0RatChunk000Sub001First100_eq_blocks

def surrogateDiagonalTailChunk000Sub001First250Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001First100Sum X0
    + surrogateDiagonalTailChunk000Sub001Block004Sum X0
    + surrogateDiagonalTailChunk000Sub001Block005Sum X0
    + surrogateDiagonalTailChunk000Sub001Block006Sum X0
    + surrogateDiagonalTailChunk000Sub001Block007Sum X0
    + surrogateDiagonalTailChunk000Sub001Block008Sum X0
    + surrogateDiagonalTailChunk000Sub001Block009Sum X0

def surrogateDiagTailX0RatChunk000Sub001First250 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001First100
    + surrogateDiagTailX0RatChunk000Sub001Block004
    + surrogateDiagTailX0RatChunk000Sub001Block005
    + surrogateDiagTailX0RatChunk000Sub001Block006
    + surrogateDiagTailX0RatChunk000Sub001Block007
    + surrogateDiagTailX0RatChunk000Sub001Block008
    + surrogateDiagTailX0RatChunk000Sub001Block009

theorem surrogateDiagTailX0RatChunk000Sub001First250_eq_blocks :
    surrogateDiagTailX0RatChunk000Sub001First100
      + surrogateDiagTailX0RatChunk000Sub001Block004
      + surrogateDiagTailX0RatChunk000Sub001Block005
      + surrogateDiagTailX0RatChunk000Sub001Block006
      + surrogateDiagTailX0RatChunk000Sub001Block007
      + surrogateDiagTailX0RatChunk000Sub001Block008
      + surrogateDiagTailX0RatChunk000Sub001Block009
      = surrogateDiagTailX0RatChunk000Sub001First250 := by
  unfold surrogateDiagTailX0RatChunk000Sub001First250
  ring

def SurrogateDiagonalTailChunk000Sub001First250CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001First250Sum X0 = surrogateDiagTailX0RatChunk000Sub001First250

def SurrogateDiagonalTailChunk000Sub001Block004CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block004Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block004
def SurrogateDiagonalTailChunk000Sub001Block005CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block005Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block005
def SurrogateDiagonalTailChunk000Sub001Block006CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block006Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block006
def SurrogateDiagonalTailChunk000Sub001Block007CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block007Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block007
def SurrogateDiagonalTailChunk000Sub001Block008CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block008Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block008
def SurrogateDiagonalTailChunk000Sub001Block009CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block009Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block009

theorem surrogateDiagonalTailChunk000Sub001First250_eq_cert_explicit
    (hFirst100 : SurrogateDiagonalTailChunk000Sub001First100CertificateAt X0)
    (hBlock004 : SurrogateDiagonalTailChunk000Sub001Block004CertificateAt X0)
    (hBlock005 : SurrogateDiagonalTailChunk000Sub001Block005CertificateAt X0)
    (hBlock006 : SurrogateDiagonalTailChunk000Sub001Block006CertificateAt X0)
    (hBlock007 : SurrogateDiagonalTailChunk000Sub001Block007CertificateAt X0)
    (hBlock008 : SurrogateDiagonalTailChunk000Sub001Block008CertificateAt X0)
    (hBlock009 : SurrogateDiagonalTailChunk000Sub001Block009CertificateAt X0)
    : surrogateDiagonalTailChunk000Sub001First250Sum X0 = surrogateDiagTailX0RatChunk000Sub001First250 := by
  unfold SurrogateDiagonalTailChunk000Sub001First100CertificateAt at hFirst100
  unfold SurrogateDiagonalTailChunk000Sub001Block004CertificateAt at hBlock004
  unfold SurrogateDiagonalTailChunk000Sub001Block005CertificateAt at hBlock005
  unfold SurrogateDiagonalTailChunk000Sub001Block006CertificateAt at hBlock006
  unfold SurrogateDiagonalTailChunk000Sub001Block007CertificateAt at hBlock007
  unfold SurrogateDiagonalTailChunk000Sub001Block008CertificateAt at hBlock008
  unfold SurrogateDiagonalTailChunk000Sub001Block009CertificateAt at hBlock009
  unfold surrogateDiagonalTailChunk000Sub001First250Sum
  rw [hFirst100, hBlock004, hBlock005, hBlock006, hBlock007, hBlock008, hBlock009]
  exact surrogateDiagTailX0RatChunk000Sub001First250_eq_blocks

def surrogateDiagonalTailChunk000Sub001First500Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001First250Sum X0
    + surrogateDiagonalTailChunk000Sub001Block010Sum X0
    + surrogateDiagonalTailChunk000Sub001Block011Sum X0
    + surrogateDiagonalTailChunk000Sub001Block012Sum X0
    + surrogateDiagonalTailChunk000Sub001Block013Sum X0
    + surrogateDiagonalTailChunk000Sub001Block014Sum X0
    + surrogateDiagonalTailChunk000Sub001Block015Sum X0
    + surrogateDiagonalTailChunk000Sub001Block016Sum X0
    + surrogateDiagonalTailChunk000Sub001Block017Sum X0
    + surrogateDiagonalTailChunk000Sub001Block018Sum X0
    + surrogateDiagonalTailChunk000Sub001Block019Sum X0

def surrogateDiagTailX0RatChunk000Sub001First500 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001First250
    + surrogateDiagTailX0RatChunk000Sub001Block010
    + surrogateDiagTailX0RatChunk000Sub001Block011
    + surrogateDiagTailX0RatChunk000Sub001Block012
    + surrogateDiagTailX0RatChunk000Sub001Block013
    + surrogateDiagTailX0RatChunk000Sub001Block014
    + surrogateDiagTailX0RatChunk000Sub001Block015
    + surrogateDiagTailX0RatChunk000Sub001Block016
    + surrogateDiagTailX0RatChunk000Sub001Block017
    + surrogateDiagTailX0RatChunk000Sub001Block018
    + surrogateDiagTailX0RatChunk000Sub001Block019

theorem surrogateDiagTailX0RatChunk000Sub001First500_eq_blocks :
    surrogateDiagTailX0RatChunk000Sub001First250
      + surrogateDiagTailX0RatChunk000Sub001Block010
      + surrogateDiagTailX0RatChunk000Sub001Block011
      + surrogateDiagTailX0RatChunk000Sub001Block012
      + surrogateDiagTailX0RatChunk000Sub001Block013
      + surrogateDiagTailX0RatChunk000Sub001Block014
      + surrogateDiagTailX0RatChunk000Sub001Block015
      + surrogateDiagTailX0RatChunk000Sub001Block016
      + surrogateDiagTailX0RatChunk000Sub001Block017
      + surrogateDiagTailX0RatChunk000Sub001Block018
      + surrogateDiagTailX0RatChunk000Sub001Block019
      = surrogateDiagTailX0RatChunk000Sub001First500 := by
  unfold surrogateDiagTailX0RatChunk000Sub001First500
  ring

def SurrogateDiagonalTailChunk000Sub001First500CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001First500Sum X0 = surrogateDiagTailX0RatChunk000Sub001First500

def SurrogateDiagonalTailChunk000Sub001Block010CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block010Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block010
def SurrogateDiagonalTailChunk000Sub001Block011CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block011Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block011
def SurrogateDiagonalTailChunk000Sub001Block012CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block012Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block012
def SurrogateDiagonalTailChunk000Sub001Block013CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block013Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block013
def SurrogateDiagonalTailChunk000Sub001Block014CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block014Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block014
def SurrogateDiagonalTailChunk000Sub001Block015CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block015Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block015
def SurrogateDiagonalTailChunk000Sub001Block016CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block016Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block016
def SurrogateDiagonalTailChunk000Sub001Block017CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block017Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block017
def SurrogateDiagonalTailChunk000Sub001Block018CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block018Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block018
def SurrogateDiagonalTailChunk000Sub001Block019CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block019Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block019

theorem surrogateDiagonalTailChunk000Sub001First500_eq_cert_explicit
    (hFirst250 : SurrogateDiagonalTailChunk000Sub001First250CertificateAt X0)
    (hBlock010 : SurrogateDiagonalTailChunk000Sub001Block010CertificateAt X0)
    (hBlock011 : SurrogateDiagonalTailChunk000Sub001Block011CertificateAt X0)
    (hBlock012 : SurrogateDiagonalTailChunk000Sub001Block012CertificateAt X0)
    (hBlock013 : SurrogateDiagonalTailChunk000Sub001Block013CertificateAt X0)
    (hBlock014 : SurrogateDiagonalTailChunk000Sub001Block014CertificateAt X0)
    (hBlock015 : SurrogateDiagonalTailChunk000Sub001Block015CertificateAt X0)
    (hBlock016 : SurrogateDiagonalTailChunk000Sub001Block016CertificateAt X0)
    (hBlock017 : SurrogateDiagonalTailChunk000Sub001Block017CertificateAt X0)
    (hBlock018 : SurrogateDiagonalTailChunk000Sub001Block018CertificateAt X0)
    (hBlock019 : SurrogateDiagonalTailChunk000Sub001Block019CertificateAt X0)
    : surrogateDiagonalTailChunk000Sub001First500Sum X0 = surrogateDiagTailX0RatChunk000Sub001First500 := by
  unfold SurrogateDiagonalTailChunk000Sub001First250CertificateAt at hFirst250
  unfold SurrogateDiagonalTailChunk000Sub001Block010CertificateAt at hBlock010
  unfold SurrogateDiagonalTailChunk000Sub001Block011CertificateAt at hBlock011
  unfold SurrogateDiagonalTailChunk000Sub001Block012CertificateAt at hBlock012
  unfold SurrogateDiagonalTailChunk000Sub001Block013CertificateAt at hBlock013
  unfold SurrogateDiagonalTailChunk000Sub001Block014CertificateAt at hBlock014
  unfold SurrogateDiagonalTailChunk000Sub001Block015CertificateAt at hBlock015
  unfold SurrogateDiagonalTailChunk000Sub001Block016CertificateAt at hBlock016
  unfold SurrogateDiagonalTailChunk000Sub001Block017CertificateAt at hBlock017
  unfold SurrogateDiagonalTailChunk000Sub001Block018CertificateAt at hBlock018
  unfold SurrogateDiagonalTailChunk000Sub001Block019CertificateAt at hBlock019
  unfold surrogateDiagonalTailChunk000Sub001First500Sum
  rw [hFirst250, hBlock010, hBlock011, hBlock012, hBlock013, hBlock014, hBlock015, hBlock016, hBlock017, hBlock018, hBlock019]
  exact surrogateDiagTailX0RatChunk000Sub001First500_eq_blocks

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001Band000_009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001Band010_019

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk001Sub001First250Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block000Sum X0
    + surrogateDiagonalTailChunk001Sub001Block001Sum X0
    + surrogateDiagonalTailChunk001Sub001Block002Sum X0
    + surrogateDiagonalTailChunk001Sub001Block003Sum X0
    + surrogateDiagonalTailChunk001Sub001Block004Sum X0
    + surrogateDiagonalTailChunk001Sub001Block005Sum X0
    + surrogateDiagonalTailChunk001Sub001Block006Sum X0
    + surrogateDiagonalTailChunk001Sub001Block007Sum X0
    + surrogateDiagonalTailChunk001Sub001Block008Sum X0
    + surrogateDiagonalTailChunk001Sub001Block009Sum X0

def surrogateDiagTailX0RatChunk001Sub001First250 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block000
    + surrogateDiagTailX0RatChunk001Sub001Block001
    + surrogateDiagTailX0RatChunk001Sub001Block002
    + surrogateDiagTailX0RatChunk001Sub001Block003
    + surrogateDiagTailX0RatChunk001Sub001Block004
    + surrogateDiagTailX0RatChunk001Sub001Block005
    + surrogateDiagTailX0RatChunk001Sub001Block006
    + surrogateDiagTailX0RatChunk001Sub001Block007
    + surrogateDiagTailX0RatChunk001Sub001Block008
    + surrogateDiagTailX0RatChunk001Sub001Block009

theorem surrogateDiagTailX0RatChunk001Sub001First250_eq_blocks :
    surrogateDiagTailX0RatChunk001Sub001Block000
      + surrogateDiagTailX0RatChunk001Sub001Block001
      + surrogateDiagTailX0RatChunk001Sub001Block002
      + surrogateDiagTailX0RatChunk001Sub001Block003
      + surrogateDiagTailX0RatChunk001Sub001Block004
      + surrogateDiagTailX0RatChunk001Sub001Block005
      + surrogateDiagTailX0RatChunk001Sub001Block006
      + surrogateDiagTailX0RatChunk001Sub001Block007
      + surrogateDiagTailX0RatChunk001Sub001Block008
      + surrogateDiagTailX0RatChunk001Sub001Block009
      = surrogateDiagTailX0RatChunk001Sub001First250 := by
  unfold surrogateDiagTailX0RatChunk001Sub001First250
  ring

def SurrogateDiagonalTailChunk001Sub001Block000CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block000Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block000
def SurrogateDiagonalTailChunk001Sub001Block001CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block001Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block001
def SurrogateDiagonalTailChunk001Sub001Block002CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block002Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block002
def SurrogateDiagonalTailChunk001Sub001Block003CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block003Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block003
def SurrogateDiagonalTailChunk001Sub001Block004CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block004Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block004
def SurrogateDiagonalTailChunk001Sub001Block005CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block005Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block005
def SurrogateDiagonalTailChunk001Sub001Block006CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block006Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block006
def SurrogateDiagonalTailChunk001Sub001Block007CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block007Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block007
def SurrogateDiagonalTailChunk001Sub001Block008CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block008Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block008
def SurrogateDiagonalTailChunk001Sub001Block009CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block009Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block009

def SurrogateDiagonalTailChunk001Sub001First250CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001First250Sum X0 = surrogateDiagTailX0RatChunk001Sub001First250

theorem surrogateDiagonalTailChunk001Sub001First250_eq_cert_explicit
    (hBlock000 : SurrogateDiagonalTailChunk001Sub001Block000CertificateAt X0)
    (hBlock001 : SurrogateDiagonalTailChunk001Sub001Block001CertificateAt X0)
    (hBlock002 : SurrogateDiagonalTailChunk001Sub001Block002CertificateAt X0)
    (hBlock003 : SurrogateDiagonalTailChunk001Sub001Block003CertificateAt X0)
    (hBlock004 : SurrogateDiagonalTailChunk001Sub001Block004CertificateAt X0)
    (hBlock005 : SurrogateDiagonalTailChunk001Sub001Block005CertificateAt X0)
    (hBlock006 : SurrogateDiagonalTailChunk001Sub001Block006CertificateAt X0)
    (hBlock007 : SurrogateDiagonalTailChunk001Sub001Block007CertificateAt X0)
    (hBlock008 : SurrogateDiagonalTailChunk001Sub001Block008CertificateAt X0)
    (hBlock009 : SurrogateDiagonalTailChunk001Sub001Block009CertificateAt X0)
    : surrogateDiagonalTailChunk001Sub001First250Sum X0 = surrogateDiagTailX0RatChunk001Sub001First250 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block000CertificateAt at hBlock000
  unfold SurrogateDiagonalTailChunk001Sub001Block001CertificateAt at hBlock001
  unfold SurrogateDiagonalTailChunk001Sub001Block002CertificateAt at hBlock002
  unfold SurrogateDiagonalTailChunk001Sub001Block003CertificateAt at hBlock003
  unfold SurrogateDiagonalTailChunk001Sub001Block004CertificateAt at hBlock004
  unfold SurrogateDiagonalTailChunk001Sub001Block005CertificateAt at hBlock005
  unfold SurrogateDiagonalTailChunk001Sub001Block006CertificateAt at hBlock006
  unfold SurrogateDiagonalTailChunk001Sub001Block007CertificateAt at hBlock007
  unfold SurrogateDiagonalTailChunk001Sub001Block008CertificateAt at hBlock008
  unfold SurrogateDiagonalTailChunk001Sub001Block009CertificateAt at hBlock009
  unfold surrogateDiagonalTailChunk001Sub001First250Sum
  rw [hBlock000, hBlock001, hBlock002, hBlock003, hBlock004, hBlock005, hBlock006, hBlock007, hBlock008, hBlock009]
  exact surrogateDiagTailX0RatChunk001Sub001First250_eq_blocks

def surrogateDiagonalTailChunk001Sub001First500Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001First250Sum X0
    + surrogateDiagonalTailChunk001Sub001Block010Sum X0
    + surrogateDiagonalTailChunk001Sub001Block011Sum X0
    + surrogateDiagonalTailChunk001Sub001Block012Sum X0
    + surrogateDiagonalTailChunk001Sub001Block013Sum X0
    + surrogateDiagonalTailChunk001Sub001Block014Sum X0
    + surrogateDiagonalTailChunk001Sub001Block015Sum X0
    + surrogateDiagonalTailChunk001Sub001Block016Sum X0
    + surrogateDiagonalTailChunk001Sub001Block017Sum X0
    + surrogateDiagonalTailChunk001Sub001Block018Sum X0
    + surrogateDiagonalTailChunk001Sub001Block019Sum X0

def surrogateDiagTailX0RatChunk001Sub001First500 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001First250
    + surrogateDiagTailX0RatChunk001Sub001Block010
    + surrogateDiagTailX0RatChunk001Sub001Block011
    + surrogateDiagTailX0RatChunk001Sub001Block012
    + surrogateDiagTailX0RatChunk001Sub001Block013
    + surrogateDiagTailX0RatChunk001Sub001Block014
    + surrogateDiagTailX0RatChunk001Sub001Block015
    + surrogateDiagTailX0RatChunk001Sub001Block016
    + surrogateDiagTailX0RatChunk001Sub001Block017
    + surrogateDiagTailX0RatChunk001Sub001Block018
    + surrogateDiagTailX0RatChunk001Sub001Block019

theorem surrogateDiagTailX0RatChunk001Sub001First500_eq_blocks :
    surrogateDiagTailX0RatChunk001Sub001First250
      + surrogateDiagTailX0RatChunk001Sub001Block010
      + surrogateDiagTailX0RatChunk001Sub001Block011
      + surrogateDiagTailX0RatChunk001Sub001Block012
      + surrogateDiagTailX0RatChunk001Sub001Block013
      + surrogateDiagTailX0RatChunk001Sub001Block014
      + surrogateDiagTailX0RatChunk001Sub001Block015
      + surrogateDiagTailX0RatChunk001Sub001Block016
      + surrogateDiagTailX0RatChunk001Sub001Block017
      + surrogateDiagTailX0RatChunk001Sub001Block018
      + surrogateDiagTailX0RatChunk001Sub001Block019
      = surrogateDiagTailX0RatChunk001Sub001First500 := by
  unfold surrogateDiagTailX0RatChunk001Sub001First500
  ring

def SurrogateDiagonalTailChunk001Sub001First500CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001First500Sum X0 = surrogateDiagTailX0RatChunk001Sub001First500

def SurrogateDiagonalTailChunk001Sub001Block010CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block010Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block010
def SurrogateDiagonalTailChunk001Sub001Block011CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block011Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block011
def SurrogateDiagonalTailChunk001Sub001Block012CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block012Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block012
def SurrogateDiagonalTailChunk001Sub001Block013CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block013Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block013
def SurrogateDiagonalTailChunk001Sub001Block014CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block014Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block014
def SurrogateDiagonalTailChunk001Sub001Block015CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block015Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block015
def SurrogateDiagonalTailChunk001Sub001Block016CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block016Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block016
def SurrogateDiagonalTailChunk001Sub001Block017CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block017Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block017
def SurrogateDiagonalTailChunk001Sub001Block018CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block018Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block018
def SurrogateDiagonalTailChunk001Sub001Block019CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block019Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block019

theorem surrogateDiagonalTailChunk001Sub001First500_eq_cert_explicit
    (hFirst250 : SurrogateDiagonalTailChunk001Sub001First250CertificateAt X0)
    (hBlock010 : SurrogateDiagonalTailChunk001Sub001Block010CertificateAt X0)
    (hBlock011 : SurrogateDiagonalTailChunk001Sub001Block011CertificateAt X0)
    (hBlock012 : SurrogateDiagonalTailChunk001Sub001Block012CertificateAt X0)
    (hBlock013 : SurrogateDiagonalTailChunk001Sub001Block013CertificateAt X0)
    (hBlock014 : SurrogateDiagonalTailChunk001Sub001Block014CertificateAt X0)
    (hBlock015 : SurrogateDiagonalTailChunk001Sub001Block015CertificateAt X0)
    (hBlock016 : SurrogateDiagonalTailChunk001Sub001Block016CertificateAt X0)
    (hBlock017 : SurrogateDiagonalTailChunk001Sub001Block017CertificateAt X0)
    (hBlock018 : SurrogateDiagonalTailChunk001Sub001Block018CertificateAt X0)
    (hBlock019 : SurrogateDiagonalTailChunk001Sub001Block019CertificateAt X0)
    : surrogateDiagonalTailChunk001Sub001First500Sum X0 = surrogateDiagTailX0RatChunk001Sub001First500 := by
  unfold SurrogateDiagonalTailChunk001Sub001First250CertificateAt at hFirst250
  unfold SurrogateDiagonalTailChunk001Sub001Block010CertificateAt at hBlock010
  unfold SurrogateDiagonalTailChunk001Sub001Block011CertificateAt at hBlock011
  unfold SurrogateDiagonalTailChunk001Sub001Block012CertificateAt at hBlock012
  unfold SurrogateDiagonalTailChunk001Sub001Block013CertificateAt at hBlock013
  unfold SurrogateDiagonalTailChunk001Sub001Block014CertificateAt at hBlock014
  unfold SurrogateDiagonalTailChunk001Sub001Block015CertificateAt at hBlock015
  unfold SurrogateDiagonalTailChunk001Sub001Block016CertificateAt at hBlock016
  unfold SurrogateDiagonalTailChunk001Sub001Block017CertificateAt at hBlock017
  unfold SurrogateDiagonalTailChunk001Sub001Block018CertificateAt at hBlock018
  unfold SurrogateDiagonalTailChunk001Sub001Block019CertificateAt at hBlock019
  unfold surrogateDiagonalTailChunk001Sub001First500Sum
  rw [hFirst250, hBlock010, hBlock011, hBlock012, hBlock013, hBlock014, hBlock015, hBlock016, hBlock017, hBlock018, hBlock019]
  exact surrogateDiagTailX0RatChunk001Sub001First500_eq_blocks

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

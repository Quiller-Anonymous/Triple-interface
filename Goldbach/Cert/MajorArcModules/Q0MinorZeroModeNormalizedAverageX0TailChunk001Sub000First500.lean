import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub000Band000_009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub000Band010_019

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk001Sub000First250Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block000Sum X0
    + surrogateDiagonalTailChunk001Sub000Block001Sum X0
    + surrogateDiagonalTailChunk001Sub000Block002Sum X0
    + surrogateDiagonalTailChunk001Sub000Block003Sum X0
    + surrogateDiagonalTailChunk001Sub000Block004Sum X0
    + surrogateDiagonalTailChunk001Sub000Block005Sum X0
    + surrogateDiagonalTailChunk001Sub000Block006Sum X0
    + surrogateDiagonalTailChunk001Sub000Block007Sum X0
    + surrogateDiagonalTailChunk001Sub000Block008Sum X0
    + surrogateDiagonalTailChunk001Sub000Block009Sum X0

def surrogateDiagTailX0RatChunk001Sub000First250 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block000
    + surrogateDiagTailX0RatChunk001Sub000Block001
    + surrogateDiagTailX0RatChunk001Sub000Block002
    + surrogateDiagTailX0RatChunk001Sub000Block003
    + surrogateDiagTailX0RatChunk001Sub000Block004
    + surrogateDiagTailX0RatChunk001Sub000Block005
    + surrogateDiagTailX0RatChunk001Sub000Block006
    + surrogateDiagTailX0RatChunk001Sub000Block007
    + surrogateDiagTailX0RatChunk001Sub000Block008
    + surrogateDiagTailX0RatChunk001Sub000Block009

theorem surrogateDiagTailX0RatChunk001Sub000First250_eq_blocks :
    surrogateDiagTailX0RatChunk001Sub000Block000
      + surrogateDiagTailX0RatChunk001Sub000Block001
      + surrogateDiagTailX0RatChunk001Sub000Block002
      + surrogateDiagTailX0RatChunk001Sub000Block003
      + surrogateDiagTailX0RatChunk001Sub000Block004
      + surrogateDiagTailX0RatChunk001Sub000Block005
      + surrogateDiagTailX0RatChunk001Sub000Block006
      + surrogateDiagTailX0RatChunk001Sub000Block007
      + surrogateDiagTailX0RatChunk001Sub000Block008
      + surrogateDiagTailX0RatChunk001Sub000Block009
      = surrogateDiagTailX0RatChunk001Sub000First250 := by
  unfold surrogateDiagTailX0RatChunk001Sub000First250
  ring

def SurrogateDiagonalTailChunk001Sub000Block000CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block000Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block000
def SurrogateDiagonalTailChunk001Sub000Block001CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block001Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block001
def SurrogateDiagonalTailChunk001Sub000Block002CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block002Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block002
def SurrogateDiagonalTailChunk001Sub000Block003CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block003Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block003
def SurrogateDiagonalTailChunk001Sub000Block004CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block004Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block004
def SurrogateDiagonalTailChunk001Sub000Block005CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block005Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block005
def SurrogateDiagonalTailChunk001Sub000Block006CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block006Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block006
def SurrogateDiagonalTailChunk001Sub000Block007CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block007Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block007
def SurrogateDiagonalTailChunk001Sub000Block008CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block008Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block008
def SurrogateDiagonalTailChunk001Sub000Block009CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block009Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block009

def SurrogateDiagonalTailChunk001Sub000First250CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000First250Sum X0 = surrogateDiagTailX0RatChunk001Sub000First250

theorem surrogateDiagonalTailChunk001Sub000First250_eq_cert_explicit
    (hBlock000 : SurrogateDiagonalTailChunk001Sub000Block000CertificateAt X0)
    (hBlock001 : SurrogateDiagonalTailChunk001Sub000Block001CertificateAt X0)
    (hBlock002 : SurrogateDiagonalTailChunk001Sub000Block002CertificateAt X0)
    (hBlock003 : SurrogateDiagonalTailChunk001Sub000Block003CertificateAt X0)
    (hBlock004 : SurrogateDiagonalTailChunk001Sub000Block004CertificateAt X0)
    (hBlock005 : SurrogateDiagonalTailChunk001Sub000Block005CertificateAt X0)
    (hBlock006 : SurrogateDiagonalTailChunk001Sub000Block006CertificateAt X0)
    (hBlock007 : SurrogateDiagonalTailChunk001Sub000Block007CertificateAt X0)
    (hBlock008 : SurrogateDiagonalTailChunk001Sub000Block008CertificateAt X0)
    (hBlock009 : SurrogateDiagonalTailChunk001Sub000Block009CertificateAt X0)
    : surrogateDiagonalTailChunk001Sub000First250Sum X0 = surrogateDiagTailX0RatChunk001Sub000First250 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block000CertificateAt at hBlock000
  unfold SurrogateDiagonalTailChunk001Sub000Block001CertificateAt at hBlock001
  unfold SurrogateDiagonalTailChunk001Sub000Block002CertificateAt at hBlock002
  unfold SurrogateDiagonalTailChunk001Sub000Block003CertificateAt at hBlock003
  unfold SurrogateDiagonalTailChunk001Sub000Block004CertificateAt at hBlock004
  unfold SurrogateDiagonalTailChunk001Sub000Block005CertificateAt at hBlock005
  unfold SurrogateDiagonalTailChunk001Sub000Block006CertificateAt at hBlock006
  unfold SurrogateDiagonalTailChunk001Sub000Block007CertificateAt at hBlock007
  unfold SurrogateDiagonalTailChunk001Sub000Block008CertificateAt at hBlock008
  unfold SurrogateDiagonalTailChunk001Sub000Block009CertificateAt at hBlock009
  unfold surrogateDiagonalTailChunk001Sub000First250Sum
  rw [hBlock000, hBlock001, hBlock002, hBlock003, hBlock004, hBlock005, hBlock006, hBlock007, hBlock008, hBlock009]
  exact surrogateDiagTailX0RatChunk001Sub000First250_eq_blocks

def surrogateDiagonalTailChunk001Sub000First500Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000First250Sum X0
    + surrogateDiagonalTailChunk001Sub000Block010Sum X0
    + surrogateDiagonalTailChunk001Sub000Block011Sum X0
    + surrogateDiagonalTailChunk001Sub000Block012Sum X0
    + surrogateDiagonalTailChunk001Sub000Block013Sum X0
    + surrogateDiagonalTailChunk001Sub000Block014Sum X0
    + surrogateDiagonalTailChunk001Sub000Block015Sum X0
    + surrogateDiagonalTailChunk001Sub000Block016Sum X0
    + surrogateDiagonalTailChunk001Sub000Block017Sum X0
    + surrogateDiagonalTailChunk001Sub000Block018Sum X0
    + surrogateDiagonalTailChunk001Sub000Block019Sum X0

def surrogateDiagTailX0RatChunk001Sub000First500 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000First250
    + surrogateDiagTailX0RatChunk001Sub000Block010
    + surrogateDiagTailX0RatChunk001Sub000Block011
    + surrogateDiagTailX0RatChunk001Sub000Block012
    + surrogateDiagTailX0RatChunk001Sub000Block013
    + surrogateDiagTailX0RatChunk001Sub000Block014
    + surrogateDiagTailX0RatChunk001Sub000Block015
    + surrogateDiagTailX0RatChunk001Sub000Block016
    + surrogateDiagTailX0RatChunk001Sub000Block017
    + surrogateDiagTailX0RatChunk001Sub000Block018
    + surrogateDiagTailX0RatChunk001Sub000Block019

theorem surrogateDiagTailX0RatChunk001Sub000First500_eq_blocks :
    surrogateDiagTailX0RatChunk001Sub000First250
      + surrogateDiagTailX0RatChunk001Sub000Block010
      + surrogateDiagTailX0RatChunk001Sub000Block011
      + surrogateDiagTailX0RatChunk001Sub000Block012
      + surrogateDiagTailX0RatChunk001Sub000Block013
      + surrogateDiagTailX0RatChunk001Sub000Block014
      + surrogateDiagTailX0RatChunk001Sub000Block015
      + surrogateDiagTailX0RatChunk001Sub000Block016
      + surrogateDiagTailX0RatChunk001Sub000Block017
      + surrogateDiagTailX0RatChunk001Sub000Block018
      + surrogateDiagTailX0RatChunk001Sub000Block019
      = surrogateDiagTailX0RatChunk001Sub000First500 := by
  unfold surrogateDiagTailX0RatChunk001Sub000First500
  ring

def SurrogateDiagonalTailChunk001Sub000First500CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000First500Sum X0 = surrogateDiagTailX0RatChunk001Sub000First500

def SurrogateDiagonalTailChunk001Sub000Block010CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block010Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block010
def SurrogateDiagonalTailChunk001Sub000Block011CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block011Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block011
def SurrogateDiagonalTailChunk001Sub000Block012CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block012Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block012
def SurrogateDiagonalTailChunk001Sub000Block013CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block013Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block013
def SurrogateDiagonalTailChunk001Sub000Block014CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block014Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block014
def SurrogateDiagonalTailChunk001Sub000Block015CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block015Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block015
def SurrogateDiagonalTailChunk001Sub000Block016CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block016Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block016
def SurrogateDiagonalTailChunk001Sub000Block017CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block017Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block017
def SurrogateDiagonalTailChunk001Sub000Block018CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block018Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block018
def SurrogateDiagonalTailChunk001Sub000Block019CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block019Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block019

theorem surrogateDiagonalTailChunk001Sub000First500_eq_cert_explicit
    (hFirst250 : SurrogateDiagonalTailChunk001Sub000First250CertificateAt X0)
    (hBlock010 : SurrogateDiagonalTailChunk001Sub000Block010CertificateAt X0)
    (hBlock011 : SurrogateDiagonalTailChunk001Sub000Block011CertificateAt X0)
    (hBlock012 : SurrogateDiagonalTailChunk001Sub000Block012CertificateAt X0)
    (hBlock013 : SurrogateDiagonalTailChunk001Sub000Block013CertificateAt X0)
    (hBlock014 : SurrogateDiagonalTailChunk001Sub000Block014CertificateAt X0)
    (hBlock015 : SurrogateDiagonalTailChunk001Sub000Block015CertificateAt X0)
    (hBlock016 : SurrogateDiagonalTailChunk001Sub000Block016CertificateAt X0)
    (hBlock017 : SurrogateDiagonalTailChunk001Sub000Block017CertificateAt X0)
    (hBlock018 : SurrogateDiagonalTailChunk001Sub000Block018CertificateAt X0)
    (hBlock019 : SurrogateDiagonalTailChunk001Sub000Block019CertificateAt X0)
    : surrogateDiagonalTailChunk001Sub000First500Sum X0 = surrogateDiagTailX0RatChunk001Sub000First500 := by
  unfold SurrogateDiagonalTailChunk001Sub000First250CertificateAt at hFirst250
  unfold SurrogateDiagonalTailChunk001Sub000Block010CertificateAt at hBlock010
  unfold SurrogateDiagonalTailChunk001Sub000Block011CertificateAt at hBlock011
  unfold SurrogateDiagonalTailChunk001Sub000Block012CertificateAt at hBlock012
  unfold SurrogateDiagonalTailChunk001Sub000Block013CertificateAt at hBlock013
  unfold SurrogateDiagonalTailChunk001Sub000Block014CertificateAt at hBlock014
  unfold SurrogateDiagonalTailChunk001Sub000Block015CertificateAt at hBlock015
  unfold SurrogateDiagonalTailChunk001Sub000Block016CertificateAt at hBlock016
  unfold SurrogateDiagonalTailChunk001Sub000Block017CertificateAt at hBlock017
  unfold SurrogateDiagonalTailChunk001Sub000Block018CertificateAt at hBlock018
  unfold SurrogateDiagonalTailChunk001Sub000Block019CertificateAt at hBlock019
  unfold surrogateDiagonalTailChunk001Sub000First500Sum
  rw [hFirst250, hBlock010, hBlock011, hBlock012, hBlock013, hBlock014, hBlock015, hBlock016, hBlock017, hBlock018, hBlock019]
  exact surrogateDiagTailX0RatChunk001Sub000First500_eq_blocks

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

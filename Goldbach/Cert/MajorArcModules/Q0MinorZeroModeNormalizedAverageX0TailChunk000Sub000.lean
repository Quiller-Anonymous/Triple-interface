import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block012
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block013
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block014
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block016
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block017
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block018
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Block019

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk000Sub000First100Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Pilot25Sum X0
    + surrogateDiagonalTailChunk000Sub000Block001Sum X0
    + surrogateDiagonalTailChunk000Sub000Block002Sum X0
    + surrogateDiagonalTailChunk000Sub000Block003Sum X0

def surrogateDiagTailX0RatChunk000Sub000First100 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Pilot25
    + surrogateDiagTailX0RatChunk000Sub000Block001
    + surrogateDiagTailX0RatChunk000Sub000Block002
    + surrogateDiagTailX0RatChunk000Sub000Block003

theorem surrogateDiagTailX0RatChunk000Sub000First100_eq_blocks :
    surrogateDiagTailX0RatChunk000Sub000Pilot25
      + surrogateDiagTailX0RatChunk000Sub000Block001
      + surrogateDiagTailX0RatChunk000Sub000Block002
      + surrogateDiagTailX0RatChunk000Sub000Block003
      = surrogateDiagTailX0RatChunk000Sub000First100 := by
  unfold surrogateDiagTailX0RatChunk000Sub000First100
  ring

def SurrogateDiagonalTailChunk000Sub000Pilot25CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Pilot25Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Pilot25

def SurrogateDiagonalTailChunk000Sub000Block001CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block001Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block001

def SurrogateDiagonalTailChunk000Sub000Block002CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block002Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block002

def SurrogateDiagonalTailChunk000Sub000Block003CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block003Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block003

theorem surrogateDiagonalTailChunk000Sub000First100_eq_cert_explicit
    (hPilot25 : SurrogateDiagonalTailChunk000Sub000Pilot25CertificateAt X0)
    (hBlock001 : SurrogateDiagonalTailChunk000Sub000Block001CertificateAt X0)
    (hBlock002 : SurrogateDiagonalTailChunk000Sub000Block002CertificateAt X0)
    (hBlock003 : SurrogateDiagonalTailChunk000Sub000Block003CertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000First100Sum X0
      = surrogateDiagTailX0RatChunk000Sub000First100 := by
  unfold SurrogateDiagonalTailChunk000Sub000Pilot25CertificateAt at hPilot25
  unfold SurrogateDiagonalTailChunk000Sub000Block001CertificateAt at hBlock001
  unfold SurrogateDiagonalTailChunk000Sub000Block002CertificateAt at hBlock002
  unfold SurrogateDiagonalTailChunk000Sub000Block003CertificateAt at hBlock003
  unfold surrogateDiagonalTailChunk000Sub000First100Sum
  rw [hPilot25, hBlock001, hBlock002, hBlock003]
  exact surrogateDiagTailX0RatChunk000Sub000First100_eq_blocks

def surrogateDiagonalTailChunk000Sub000First250Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000First100Sum X0
    + surrogateDiagonalTailChunk000Sub000Block004Sum X0
    + surrogateDiagonalTailChunk000Sub000Block005Sum X0
    + surrogateDiagonalTailChunk000Sub000Block006Sum X0
    + surrogateDiagonalTailChunk000Sub000Block007Sum X0
    + surrogateDiagonalTailChunk000Sub000Block008Sum X0
    + surrogateDiagonalTailChunk000Sub000Block009Sum X0

def surrogateDiagTailX0RatChunk000Sub000First250 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000First100
    + surrogateDiagTailX0RatChunk000Sub000Block004
    + surrogateDiagTailX0RatChunk000Sub000Block005
    + surrogateDiagTailX0RatChunk000Sub000Block006
    + surrogateDiagTailX0RatChunk000Sub000Block007
    + surrogateDiagTailX0RatChunk000Sub000Block008
    + surrogateDiagTailX0RatChunk000Sub000Block009

theorem surrogateDiagTailX0RatChunk000Sub000First250_eq_blocks :
    surrogateDiagTailX0RatChunk000Sub000First100
      + surrogateDiagTailX0RatChunk000Sub000Block004
      + surrogateDiagTailX0RatChunk000Sub000Block005
      + surrogateDiagTailX0RatChunk000Sub000Block006
      + surrogateDiagTailX0RatChunk000Sub000Block007
      + surrogateDiagTailX0RatChunk000Sub000Block008
      + surrogateDiagTailX0RatChunk000Sub000Block009
      = surrogateDiagTailX0RatChunk000Sub000First250 := by
  unfold surrogateDiagTailX0RatChunk000Sub000First250
  ring

def SurrogateDiagonalTailChunk000Sub000First100CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000First100Sum X0
    = surrogateDiagTailX0RatChunk000Sub000First100

def SurrogateDiagonalTailChunk000Sub000Block004CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block004Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block004

def SurrogateDiagonalTailChunk000Sub000Block005CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block005Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block005

def SurrogateDiagonalTailChunk000Sub000Block006CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block006Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block006

def SurrogateDiagonalTailChunk000Sub000Block007CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block007Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block007

def SurrogateDiagonalTailChunk000Sub000Block008CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block008Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block008

def SurrogateDiagonalTailChunk000Sub000Block009CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block009Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block009

theorem surrogateDiagonalTailChunk000Sub000First250_eq_cert_explicit
    (hFirst100 : SurrogateDiagonalTailChunk000Sub000First100CertificateAt X0)
    (hBlock004 : SurrogateDiagonalTailChunk000Sub000Block004CertificateAt X0)
    (hBlock005 : SurrogateDiagonalTailChunk000Sub000Block005CertificateAt X0)
    (hBlock006 : SurrogateDiagonalTailChunk000Sub000Block006CertificateAt X0)
    (hBlock007 : SurrogateDiagonalTailChunk000Sub000Block007CertificateAt X0)
    (hBlock008 : SurrogateDiagonalTailChunk000Sub000Block008CertificateAt X0)
    (hBlock009 : SurrogateDiagonalTailChunk000Sub000Block009CertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000First250Sum X0
      = surrogateDiagTailX0RatChunk000Sub000First250 := by
  unfold SurrogateDiagonalTailChunk000Sub000First100CertificateAt at hFirst100
  unfold SurrogateDiagonalTailChunk000Sub000Block004CertificateAt at hBlock004
  unfold SurrogateDiagonalTailChunk000Sub000Block005CertificateAt at hBlock005
  unfold SurrogateDiagonalTailChunk000Sub000Block006CertificateAt at hBlock006
  unfold SurrogateDiagonalTailChunk000Sub000Block007CertificateAt at hBlock007
  unfold SurrogateDiagonalTailChunk000Sub000Block008CertificateAt at hBlock008
  unfold SurrogateDiagonalTailChunk000Sub000Block009CertificateAt at hBlock009
  unfold surrogateDiagonalTailChunk000Sub000First250Sum
  rw [hFirst100, hBlock004, hBlock005, hBlock006, hBlock007, hBlock008, hBlock009]
  exact surrogateDiagTailX0RatChunk000Sub000First250_eq_blocks

def surrogateDiagonalTailChunk000Sub000First500Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000First250Sum X0
    + surrogateDiagonalTailChunk000Sub000Block010Sum X0
    + surrogateDiagonalTailChunk000Sub000Block011Sum X0
    + surrogateDiagonalTailChunk000Sub000Block012Sum X0
    + surrogateDiagonalTailChunk000Sub000Block013Sum X0
    + surrogateDiagonalTailChunk000Sub000Block014Sum X0
    + surrogateDiagonalTailChunk000Sub000Block015Sum X0
    + surrogateDiagonalTailChunk000Sub000Block016Sum X0
    + surrogateDiagonalTailChunk000Sub000Block017Sum X0
    + surrogateDiagonalTailChunk000Sub000Block018Sum X0
    + surrogateDiagonalTailChunk000Sub000Block019Sum X0

def surrogateDiagTailX0RatChunk000Sub000First500 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000First250
    + surrogateDiagTailX0RatChunk000Sub000Block010
    + surrogateDiagTailX0RatChunk000Sub000Block011
    + surrogateDiagTailX0RatChunk000Sub000Block012
    + surrogateDiagTailX0RatChunk000Sub000Block013
    + surrogateDiagTailX0RatChunk000Sub000Block014
    + surrogateDiagTailX0RatChunk000Sub000Block015
    + surrogateDiagTailX0RatChunk000Sub000Block016
    + surrogateDiagTailX0RatChunk000Sub000Block017
    + surrogateDiagTailX0RatChunk000Sub000Block018
    + surrogateDiagTailX0RatChunk000Sub000Block019

theorem surrogateDiagTailX0RatChunk000Sub000First500_eq_blocks :
    surrogateDiagTailX0RatChunk000Sub000First250
      + surrogateDiagTailX0RatChunk000Sub000Block010
      + surrogateDiagTailX0RatChunk000Sub000Block011
      + surrogateDiagTailX0RatChunk000Sub000Block012
      + surrogateDiagTailX0RatChunk000Sub000Block013
      + surrogateDiagTailX0RatChunk000Sub000Block014
      + surrogateDiagTailX0RatChunk000Sub000Block015
      + surrogateDiagTailX0RatChunk000Sub000Block016
      + surrogateDiagTailX0RatChunk000Sub000Block017
      + surrogateDiagTailX0RatChunk000Sub000Block018
      + surrogateDiagTailX0RatChunk000Sub000Block019
      = surrogateDiagTailX0RatChunk000Sub000First500 := by
  unfold surrogateDiagTailX0RatChunk000Sub000First500
  ring

def SurrogateDiagonalTailChunk000Sub000First250CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000First250Sum X0
    = surrogateDiagTailX0RatChunk000Sub000First250

def SurrogateDiagonalTailChunk000Sub000Block010CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block010Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block010

def SurrogateDiagonalTailChunk000Sub000Block011CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block011Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block011

def SurrogateDiagonalTailChunk000Sub000Block012CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block012Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block012

def SurrogateDiagonalTailChunk000Sub000Block013CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block013Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block013

def SurrogateDiagonalTailChunk000Sub000Block014CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block014Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block014

def SurrogateDiagonalTailChunk000Sub000Block015CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block015Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block015

def SurrogateDiagonalTailChunk000Sub000Block016CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block016Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block016

def SurrogateDiagonalTailChunk000Sub000Block017CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block017Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block017

def SurrogateDiagonalTailChunk000Sub000Block018CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block018Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block018

def SurrogateDiagonalTailChunk000Sub000Block019CertificateAt
    (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block019Sum X0
    = surrogateDiagTailX0RatChunk000Sub000Block019

theorem surrogateDiagonalTailChunk000Sub000First500_eq_cert_explicit
    (hFirst250 : SurrogateDiagonalTailChunk000Sub000First250CertificateAt X0)
    (hBlock010 : SurrogateDiagonalTailChunk000Sub000Block010CertificateAt X0)
    (hBlock011 : SurrogateDiagonalTailChunk000Sub000Block011CertificateAt X0)
    (hBlock012 : SurrogateDiagonalTailChunk000Sub000Block012CertificateAt X0)
    (hBlock013 : SurrogateDiagonalTailChunk000Sub000Block013CertificateAt X0)
    (hBlock014 : SurrogateDiagonalTailChunk000Sub000Block014CertificateAt X0)
    (hBlock015 : SurrogateDiagonalTailChunk000Sub000Block015CertificateAt X0)
    (hBlock016 : SurrogateDiagonalTailChunk000Sub000Block016CertificateAt X0)
    (hBlock017 : SurrogateDiagonalTailChunk000Sub000Block017CertificateAt X0)
    (hBlock018 : SurrogateDiagonalTailChunk000Sub000Block018CertificateAt X0)
    (hBlock019 : SurrogateDiagonalTailChunk000Sub000Block019CertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000First500Sum X0
      = surrogateDiagTailX0RatChunk000Sub000First500 := by
  unfold SurrogateDiagonalTailChunk000Sub000First250CertificateAt at hFirst250
  unfold SurrogateDiagonalTailChunk000Sub000Block010CertificateAt at hBlock010
  unfold SurrogateDiagonalTailChunk000Sub000Block011CertificateAt at hBlock011
  unfold SurrogateDiagonalTailChunk000Sub000Block012CertificateAt at hBlock012
  unfold SurrogateDiagonalTailChunk000Sub000Block013CertificateAt at hBlock013
  unfold SurrogateDiagonalTailChunk000Sub000Block014CertificateAt at hBlock014
  unfold SurrogateDiagonalTailChunk000Sub000Block015CertificateAt at hBlock015
  unfold SurrogateDiagonalTailChunk000Sub000Block016CertificateAt at hBlock016
  unfold SurrogateDiagonalTailChunk000Sub000Block017CertificateAt at hBlock017
  unfold SurrogateDiagonalTailChunk000Sub000Block018CertificateAt at hBlock018
  unfold SurrogateDiagonalTailChunk000Sub000Block019CertificateAt at hBlock019
  unfold surrogateDiagonalTailChunk000Sub000First500Sum
  rw [hFirst250, hBlock010, hBlock011, hBlock012, hBlock013, hBlock014, hBlock015,
    hBlock016, hBlock017, hBlock018, hBlock019]
  exact surrogateDiagTailX0RatChunk000Sub000First500_eq_blocks

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

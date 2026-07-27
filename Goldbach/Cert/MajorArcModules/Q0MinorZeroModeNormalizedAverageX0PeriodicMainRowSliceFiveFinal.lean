import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup012
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup013
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup014
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup016
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup017
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup018
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup019
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveGroup020

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

namespace RowSliceFivePayload

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Final q=5 row-slice assembly over the generated group payloads. -/

def RowSliceFiveGroupsPairsUpTo000 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroup000Pairs

def RowSliceFiveGroupsTotalUpTo000 : ℚ :=
  RowSliceFiveGroup000Total

theorem RowSliceFiveGroupsUpTo000_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo000,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo000 := by
  simpa [RowSliceFiveGroupsPairsUpTo000, RowSliceFiveGroupsTotalUpTo000]
    using rowSliceFiveGroup000_actual_sum

def RowSliceFiveGroupsPairsUpTo001 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo000 ∪ RowSliceFiveGroup001Pairs

def RowSliceFiveGroupsTotalUpTo001 : ℚ :=
  RowSliceFiveGroupsTotalUpTo000 + RowSliceFiveGroup001Total

theorem RowSliceFiveGroupsPairsUpTo000_disjoint_RowSliceFiveGroup001Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo000 RowSliceFiveGroup001Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo001_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo001,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo001 := by
  rw [RowSliceFiveGroupsPairsUpTo001,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo000_disjoint_RowSliceFiveGroup001Pairs]
  rw [RowSliceFiveGroupsUpTo000_actual_sum, rowSliceFiveGroup001_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo002 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo001 ∪ RowSliceFiveGroup002Pairs

def RowSliceFiveGroupsTotalUpTo002 : ℚ :=
  RowSliceFiveGroupsTotalUpTo001 + RowSliceFiveGroup002Total

theorem RowSliceFiveGroupsPairsUpTo001_disjoint_RowSliceFiveGroup002Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo001 RowSliceFiveGroup002Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo002_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo002,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo002 := by
  rw [RowSliceFiveGroupsPairsUpTo002,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo001_disjoint_RowSliceFiveGroup002Pairs]
  rw [RowSliceFiveGroupsUpTo001_actual_sum, rowSliceFiveGroup002_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo003 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo002 ∪ RowSliceFiveGroup003Pairs

def RowSliceFiveGroupsTotalUpTo003 : ℚ :=
  RowSliceFiveGroupsTotalUpTo002 + RowSliceFiveGroup003Total

theorem RowSliceFiveGroupsPairsUpTo002_disjoint_RowSliceFiveGroup003Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo002 RowSliceFiveGroup003Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo003_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo003,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo003 := by
  rw [RowSliceFiveGroupsPairsUpTo003,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo002_disjoint_RowSliceFiveGroup003Pairs]
  rw [RowSliceFiveGroupsUpTo002_actual_sum, rowSliceFiveGroup003_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo004 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo003 ∪ RowSliceFiveGroup004Pairs

def RowSliceFiveGroupsTotalUpTo004 : ℚ :=
  RowSliceFiveGroupsTotalUpTo003 + RowSliceFiveGroup004Total

theorem RowSliceFiveGroupsPairsUpTo003_disjoint_RowSliceFiveGroup004Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo003 RowSliceFiveGroup004Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo004_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo004,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo004 := by
  rw [RowSliceFiveGroupsPairsUpTo004,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo003_disjoint_RowSliceFiveGroup004Pairs]
  rw [RowSliceFiveGroupsUpTo003_actual_sum, rowSliceFiveGroup004_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo005 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo004 ∪ RowSliceFiveGroup005Pairs

def RowSliceFiveGroupsTotalUpTo005 : ℚ :=
  RowSliceFiveGroupsTotalUpTo004 + RowSliceFiveGroup005Total

theorem RowSliceFiveGroupsPairsUpTo004_disjoint_RowSliceFiveGroup005Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo004 RowSliceFiveGroup005Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo005_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo005,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo005 := by
  rw [RowSliceFiveGroupsPairsUpTo005,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo004_disjoint_RowSliceFiveGroup005Pairs]
  rw [RowSliceFiveGroupsUpTo004_actual_sum, rowSliceFiveGroup005_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo006 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo005 ∪ RowSliceFiveGroup006Pairs

def RowSliceFiveGroupsTotalUpTo006 : ℚ :=
  RowSliceFiveGroupsTotalUpTo005 + RowSliceFiveGroup006Total

theorem RowSliceFiveGroupsPairsUpTo005_disjoint_RowSliceFiveGroup006Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo005 RowSliceFiveGroup006Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo006_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo006,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo006 := by
  rw [RowSliceFiveGroupsPairsUpTo006,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo005_disjoint_RowSliceFiveGroup006Pairs]
  rw [RowSliceFiveGroupsUpTo005_actual_sum, rowSliceFiveGroup006_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo007 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo006 ∪ RowSliceFiveGroup007Pairs

def RowSliceFiveGroupsTotalUpTo007 : ℚ :=
  RowSliceFiveGroupsTotalUpTo006 + RowSliceFiveGroup007Total

theorem RowSliceFiveGroupsPairsUpTo006_disjoint_RowSliceFiveGroup007Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo006 RowSliceFiveGroup007Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo007_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo007,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo007 := by
  rw [RowSliceFiveGroupsPairsUpTo007,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo006_disjoint_RowSliceFiveGroup007Pairs]
  rw [RowSliceFiveGroupsUpTo006_actual_sum, rowSliceFiveGroup007_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo008 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo007 ∪ RowSliceFiveGroup008Pairs

def RowSliceFiveGroupsTotalUpTo008 : ℚ :=
  RowSliceFiveGroupsTotalUpTo007 + RowSliceFiveGroup008Total

theorem RowSliceFiveGroupsPairsUpTo007_disjoint_RowSliceFiveGroup008Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo007 RowSliceFiveGroup008Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo008_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo008,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo008 := by
  rw [RowSliceFiveGroupsPairsUpTo008,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo007_disjoint_RowSliceFiveGroup008Pairs]
  rw [RowSliceFiveGroupsUpTo007_actual_sum, rowSliceFiveGroup008_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo009 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo008 ∪ RowSliceFiveGroup009Pairs

def RowSliceFiveGroupsTotalUpTo009 : ℚ :=
  RowSliceFiveGroupsTotalUpTo008 + RowSliceFiveGroup009Total

theorem RowSliceFiveGroupsPairsUpTo008_disjoint_RowSliceFiveGroup009Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo008 RowSliceFiveGroup009Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo009_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo009,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo009 := by
  rw [RowSliceFiveGroupsPairsUpTo009,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo008_disjoint_RowSliceFiveGroup009Pairs]
  rw [RowSliceFiveGroupsUpTo008_actual_sum, rowSliceFiveGroup009_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo010 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo009 ∪ RowSliceFiveGroup010Pairs

def RowSliceFiveGroupsTotalUpTo010 : ℚ :=
  RowSliceFiveGroupsTotalUpTo009 + RowSliceFiveGroup010Total

theorem RowSliceFiveGroupsPairsUpTo009_disjoint_RowSliceFiveGroup010Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo009 RowSliceFiveGroup010Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo010_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo010,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo010 := by
  rw [RowSliceFiveGroupsPairsUpTo010,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo009_disjoint_RowSliceFiveGroup010Pairs]
  rw [RowSliceFiveGroupsUpTo009_actual_sum, rowSliceFiveGroup010_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo011 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo010 ∪ RowSliceFiveGroup011Pairs

def RowSliceFiveGroupsTotalUpTo011 : ℚ :=
  RowSliceFiveGroupsTotalUpTo010 + RowSliceFiveGroup011Total

theorem RowSliceFiveGroupsPairsUpTo010_disjoint_RowSliceFiveGroup011Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo010 RowSliceFiveGroup011Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo011_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo011,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo011 := by
  rw [RowSliceFiveGroupsPairsUpTo011,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo010_disjoint_RowSliceFiveGroup011Pairs]
  rw [RowSliceFiveGroupsUpTo010_actual_sum, rowSliceFiveGroup011_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo012 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo011 ∪ RowSliceFiveGroup012Pairs

def RowSliceFiveGroupsTotalUpTo012 : ℚ :=
  RowSliceFiveGroupsTotalUpTo011 + RowSliceFiveGroup012Total

theorem RowSliceFiveGroupsPairsUpTo011_disjoint_RowSliceFiveGroup012Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo011 RowSliceFiveGroup012Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo012_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo012,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo012 := by
  rw [RowSliceFiveGroupsPairsUpTo012,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo011_disjoint_RowSliceFiveGroup012Pairs]
  rw [RowSliceFiveGroupsUpTo011_actual_sum, rowSliceFiveGroup012_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo013 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo012 ∪ RowSliceFiveGroup013Pairs

def RowSliceFiveGroupsTotalUpTo013 : ℚ :=
  RowSliceFiveGroupsTotalUpTo012 + RowSliceFiveGroup013Total

theorem RowSliceFiveGroupsPairsUpTo012_disjoint_RowSliceFiveGroup013Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo012 RowSliceFiveGroup013Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo013_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo013,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo013 := by
  rw [RowSliceFiveGroupsPairsUpTo013,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo012_disjoint_RowSliceFiveGroup013Pairs]
  rw [RowSliceFiveGroupsUpTo012_actual_sum, rowSliceFiveGroup013_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo014 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo013 ∪ RowSliceFiveGroup014Pairs

def RowSliceFiveGroupsTotalUpTo014 : ℚ :=
  RowSliceFiveGroupsTotalUpTo013 + RowSliceFiveGroup014Total

theorem RowSliceFiveGroupsPairsUpTo013_disjoint_RowSliceFiveGroup014Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo013 RowSliceFiveGroup014Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo014_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo014,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo014 := by
  rw [RowSliceFiveGroupsPairsUpTo014,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo013_disjoint_RowSliceFiveGroup014Pairs]
  rw [RowSliceFiveGroupsUpTo013_actual_sum, rowSliceFiveGroup014_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo015 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo014 ∪ RowSliceFiveGroup015Pairs

def RowSliceFiveGroupsTotalUpTo015 : ℚ :=
  RowSliceFiveGroupsTotalUpTo014 + RowSliceFiveGroup015Total

theorem RowSliceFiveGroupsPairsUpTo014_disjoint_RowSliceFiveGroup015Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo014 RowSliceFiveGroup015Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo015_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo015,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo015 := by
  rw [RowSliceFiveGroupsPairsUpTo015,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo014_disjoint_RowSliceFiveGroup015Pairs]
  rw [RowSliceFiveGroupsUpTo014_actual_sum, rowSliceFiveGroup015_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo016 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo015 ∪ RowSliceFiveGroup016Pairs

def RowSliceFiveGroupsTotalUpTo016 : ℚ :=
  RowSliceFiveGroupsTotalUpTo015 + RowSliceFiveGroup016Total

theorem RowSliceFiveGroupsPairsUpTo015_disjoint_RowSliceFiveGroup016Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo015 RowSliceFiveGroup016Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo016_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo016,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo016 := by
  rw [RowSliceFiveGroupsPairsUpTo016,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo015_disjoint_RowSliceFiveGroup016Pairs]
  rw [RowSliceFiveGroupsUpTo015_actual_sum, rowSliceFiveGroup016_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo017 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo016 ∪ RowSliceFiveGroup017Pairs

def RowSliceFiveGroupsTotalUpTo017 : ℚ :=
  RowSliceFiveGroupsTotalUpTo016 + RowSliceFiveGroup017Total

theorem RowSliceFiveGroupsPairsUpTo016_disjoint_RowSliceFiveGroup017Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo016 RowSliceFiveGroup017Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo017_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo017,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo017 := by
  rw [RowSliceFiveGroupsPairsUpTo017,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo016_disjoint_RowSliceFiveGroup017Pairs]
  rw [RowSliceFiveGroupsUpTo016_actual_sum, rowSliceFiveGroup017_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo018 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo017 ∪ RowSliceFiveGroup018Pairs

def RowSliceFiveGroupsTotalUpTo018 : ℚ :=
  RowSliceFiveGroupsTotalUpTo017 + RowSliceFiveGroup018Total

theorem RowSliceFiveGroupsPairsUpTo017_disjoint_RowSliceFiveGroup018Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo017 RowSliceFiveGroup018Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo018_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo018,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo018 := by
  rw [RowSliceFiveGroupsPairsUpTo018,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo017_disjoint_RowSliceFiveGroup018Pairs]
  rw [RowSliceFiveGroupsUpTo017_actual_sum, rowSliceFiveGroup018_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo019 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo018 ∪ RowSliceFiveGroup019Pairs

def RowSliceFiveGroupsTotalUpTo019 : ℚ :=
  RowSliceFiveGroupsTotalUpTo018 + RowSliceFiveGroup019Total

theorem RowSliceFiveGroupsPairsUpTo018_disjoint_RowSliceFiveGroup019Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo018 RowSliceFiveGroup019Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo019_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo019,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo019 := by
  rw [RowSliceFiveGroupsPairsUpTo019,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo018_disjoint_RowSliceFiveGroup019Pairs]
  rw [RowSliceFiveGroupsUpTo018_actual_sum, rowSliceFiveGroup019_actual_sum]
  rfl

def RowSliceFiveGroupsPairsUpTo020 : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo019 ∪ RowSliceFiveGroup020Pairs

def RowSliceFiveGroupsTotalUpTo020 : ℚ :=
  RowSliceFiveGroupsTotalUpTo019 + RowSliceFiveGroup020Total

theorem RowSliceFiveGroupsPairsUpTo019_disjoint_RowSliceFiveGroup020Pairs :
    Disjoint RowSliceFiveGroupsPairsUpTo019 RowSliceFiveGroup020Pairs := by
  native_decide

theorem RowSliceFiveGroupsUpTo020_actual_sum :
    (∑ p ∈ RowSliceFiveGroupsPairsUpTo020,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveGroupsTotalUpTo020 := by
  rw [RowSliceFiveGroupsPairsUpTo020,
    Finset.sum_union RowSliceFiveGroupsPairsUpTo019_disjoint_RowSliceFiveGroup020Pairs]
  rw [RowSliceFiveGroupsUpTo019_actual_sum, rowSliceFiveGroup020_actual_sum]
  rfl

def RowSliceFivePairs : Finset (ℕ × ℕ) :=
  RowSliceFiveGroupsPairsUpTo020

def RowSliceFiveTotal : ℚ :=
  RowSliceFiveGroupsTotalUpTo020

theorem rowSliceFive_actual_sum :
    (∑ p ∈ RowSliceFivePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      RowSliceFiveTotal := by
  simpa [RowSliceFivePairs, RowSliceFiveTotal] using RowSliceFiveGroupsUpTo020_actual_sum

end RowSliceFivePayload

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

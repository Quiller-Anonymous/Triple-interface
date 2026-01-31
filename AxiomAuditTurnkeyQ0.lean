import Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec

/-!
`AxiomAuditTurnkeyQ0.lean`
=========================

On-demand axiom audit for the **turnkey Q0 major-arc route**.

Build this file explicitly to print the axioms of the turnkey proof term:

`lake env lean AxiomAuditTurnkeyQ0.lean`
-/

open Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec

#check Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.turnkeyMajorArcCanon
#print axioms Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.turnkeyMajorArcCanon


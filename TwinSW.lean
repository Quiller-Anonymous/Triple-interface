/-
  TwinSW.lean
  -----------
  Optional umbrella import for the Siegel–Walfisz layer and the paper-style
  `Twin.TwinMain` bundle.  Building the `TwinSW` Lake target pulls in the
  heavy SW dependencies, while the core `Twin` library can stay lean.
-/
import Twin.AnalyticFromPaper
import Twin.MajorArc.Pin
import Twin.MajorArc.SWUniform
import Twin.SW.Characters
import Twin.SW.Defs
import Twin.SW.PartialSummation
import Twin.SW.NewUniform
import Twin.SW.SiegelWalfisz
import Twin.SW.SmoothMajorArc
import Twin.SW.DeepSW

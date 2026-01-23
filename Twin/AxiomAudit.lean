import Twin.Final
import Twin.Infinite
import Twin.Pipeline
import Twin.Assumptions
import Twin.TwinMain
import Twin.AnalyticFromPaper
import Twin.MajorArc.Pin
import Twin.ChecklistGoldDefault
import Twin.Gold

-- What’s in the final namespace?
#print prefix Twin.Final
#print prefix Twin.Infinite

-- What’s the *type* of the key theorems?
#check Twin.Final.twin_in_every_window_largeX
#check Twin.Pipeline.twins_in_all_large_windows
#check Twin.Assumptions.Analytic.twins_in_all_large_windows
#check Twin.Infinite.windows_unbounded_of_witness
#check Twin.Infinite.windows_unbounded_of_assumptions

-- What axioms (if any) do they rely on?
#print axioms Twin.Final.twin_in_every_window_largeX
#print axioms Twin.Pipeline.twins_in_all_large_windows
#print axioms Twin.Assumptions.Analytic.twins_in_all_large_windows
#print axioms Twin.Infinite.windows_unbounded_of_witness
#print axioms Twin.Infinite.windows_unbounded_of_assumptions

-- Paper-facing entry points (§§11/14 wiring)
#check Twin.Main.windows_largeX_of_errorData
#check Twin.AnalyticFromPaper.gate_onWindow_of_SME
#check Twin.MajorArc.gate_onWindow_of_SME

#print axioms Twin.Main.windows_largeX_of_errorData
#print axioms Twin.AnalyticFromPaper.gate_onWindow_of_SME
#print axioms Twin.MajorArc.gate_onWindow_of_SME

-- Checklist default entrypoint (fool's gold; axiomatized conventional inputs).
#check Twin.ChecklistGold.twins_in_all_large_windows
#check Twin.ChecklistGold.twins_in_all_large_windows_of_sme
#print axioms Twin.ChecklistGold.twins_in_all_large_windows
#print axioms Twin.ChecklistGold.twins_in_all_large_windows_of_sme

-- Twin gold-grade entrypoint (axiom-free; hypothesis-based).
#check Twin.Gold.twins_in_all_large_windows
#print axioms Twin.Gold.twins_in_all_large_windows

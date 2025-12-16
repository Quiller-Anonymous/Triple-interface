import Twin.Final
import Twin.Infinite
import Twin.Pipeline
import Twin.Assumptions

-- What’s in the final namespace?
#print prefix Twin.Final
#print prefix Twin.Infinite

-- What’s the *type* of the key theorems?
#check Twin.Final.twin_in_every_window_largeX
#check Twin.Pipeline.twins_in_all_large_windows
#check Twin.Assumptions.twins_in_all_large_windows
#check Twin.Infinite.windows_unbounded_of_witness
#check Twin.Infinite.windows_unbounded_of_assumptions

-- What axioms (if any) do they rely on?
#print axioms Twin.Final.twin_in_every_window_largeX
#print axioms Twin.Pipeline.twins_in_all_large_windows
#print axioms Twin.Assumptions.twins_in_all_large_windows
#print axioms Twin.Infinite.windows_unbounded_of_witness
#print axioms Twin.Infinite.windows_unbounded_of_assumptions

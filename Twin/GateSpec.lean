import Twin.TwinMain

namespace Twin.GateSpec

noncomputable section

open Twin

/-- Default gate spec for the frozen paper params `Twin.Main.P`. -/
noncomputable def spec : Twin.MajorArc.GateSpec Twin.Main.P :=
  Twin.MajorArc.gateCert Twin.Main.P
    (Twin.fullTruncSingularSeries Twin.Main.P.S)
    Twin.PaperParams.ss_full_pos

end

end Twin.GateSpec

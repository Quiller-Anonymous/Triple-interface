import Twin.AssemblePointwiseOnWindow
import Twin.BuildWitnessOnWindow

noncomputable section
namespace Twin.PipelineOnWindow

def witnessFrom (p : Twin.AssemblePointwiseOnWindow.Proof) :=
  Twin.BuildWitnessOnWindow.build p

end Twin.PipelineOnWindow

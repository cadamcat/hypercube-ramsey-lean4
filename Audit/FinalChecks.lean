import HypercubeRamsey.Main
import Audit.IndependentRestatement

/-!
# Final checks on the proved target

The proved `Erdos181.erdos_181` implies the independent elementary restatement of the paper's Theorem 1.1.
-/

example : FidelityProbe.Indep := FidelityProbe.fc_to_indep Erdos181.erdos_181

#print axioms Erdos181.erdos_181

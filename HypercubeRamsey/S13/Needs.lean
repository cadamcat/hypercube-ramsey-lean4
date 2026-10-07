import HypercubeRamsey.PartC.Cleaning

namespace HypercubeRamsey.S13

/-- SHARED: other-patch degree and row-tail cleaning (sections/13, lines
267–278; L12.0 and L12.6) needs the small-width discrepancy input at `xs`,
`alpha`, and slack `.04`. The existing `DeepDisc T xι αι (ι/2)` input alone
does not provide it: admissibility does not compare `xs` with `xι` or
`alpha` with `αι`. The Part C assembly already carries this input for
extraction and must pass it to stable cleaning as well. -/
def OtherPatchDiscrepancyInput (κ : CConsts) (T : Stage) : Prop :=
  DeepDisc T κ.xs κ.α 0.04

end HypercubeRamsey.S13

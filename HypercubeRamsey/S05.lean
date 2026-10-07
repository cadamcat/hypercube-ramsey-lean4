import HypercubeRamsey.S05.Defs
import HypercubeRamsey.S05.Parameters
import HypercubeRamsey.S05.Parents
import HypercubeRamsey.S05.Geometry
import HypercubeRamsey.S05.Stages
import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.S05.History
import HypercubeRamsey.S05.Selection
import HypercubeRamsey.S05.Centres
import HypercubeRamsey.S05.Clock
import HypercubeRamsey.S05.Even
import HypercubeRamsey.S05.Assembly
import HypercubeRamsey.S05.Posterior
import HypercubeRamsey.S05.Records
import HypercubeRamsey.S05.Needs

/-!
# Section 5 skeleton

Lemma 5.1 (a broad side of constant width) and its Part B one-shot export `L5_1_consumed`.  The assembly
`L5_1_rows` runs through the staged experiment: constants (D5.1), parents and streams (L5.1a), geometry and
states (L5.1b, L5.1e0, L5.1e), Steps 1–3 (L5.1c, d, f), the five conditioning stages (L5.1h1–h5) with the history
odd loads (L5.1l(1–2)), the center layer (L5.1j), the odd rows (L5.1g, L5.1k), the odd column sums (L5.1l(3)), the
clock (L5.1m), the even rows (L5.1n) and the even loads (L5.1o).
-/

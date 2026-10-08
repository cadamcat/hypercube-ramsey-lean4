import Lake
open Lake DSL

package HypercubeRamsey where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- OpenAI's library (Apache-2.0) at openai/math adc7f124, used through the shared local checkout during development.
require OAI from "../oai/lean"

@[default_target]
lean_lib HypercubeRamsey

-- The target statement (Comparator challenge module).
lean_lib Challenge

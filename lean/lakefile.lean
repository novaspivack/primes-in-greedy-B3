import Lake
open Lake DSL

package «b3-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc3"

@[default_target]
lean_lib «B3Primes» where
  roots := #[`B3Primes]

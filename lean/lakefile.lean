import Lake
open Lake DSL

package «b3-primes» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «B3Primes» where
  roots := #[`B3Primes]

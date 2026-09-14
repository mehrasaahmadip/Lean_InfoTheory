import Mathlib.Tactic

/-!
# LeanP1

Starter file. Every file under `LeanP1/` belongs to the `LeanP1` library
declared in `lakefile.toml`. A new file `LeanP1/Foo.lean` becomes part of the
build once you add `import LeanP1.Foo` to `LeanP1.lean` at the project root.
-/

namespace LeanP1

/-- Addition on natural numbers is commutative (proved by the `ring` tactic). -/
theorem add_comm' (a b : ℕ) : a + b = b + a := by
  ring

/-- Put the cursor after `by` in a proof to see the goal in the Infoview. -/
theorem two_mul_eq_add (n : ℕ) : 2 * n = n + n := by
  omega

-- `#eval` runs a computation; hover over it or check the Infoview for the result.
#eval (Finset.range 10).sum (fun i => i ^ 2)

end LeanP1

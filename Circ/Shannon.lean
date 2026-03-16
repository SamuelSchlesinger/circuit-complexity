import Circ.Internal.Bridge

/-! # Shannon Counting Lower Bound

For `N ≥ 6`, there exists a Boolean function on `N` inputs that cannot be
computed by any fan-in-2 AND/OR circuit with fewer than `2^N / (5N)` gates.

The proof proceeds by a counting (pigeonhole) argument: the number of
distinct circuits of a given size is strictly less than the number of
Boolean functions, so some function must be hard.

## Main results

The main theorem is `shannon_lower_bound_circuit`:

    theorem shannon_lower_bound_circuit (N : Nat) [NeZero N] (hN : 6 ≤ N) :
        ∃ f : BitString N → Bool,
          ∀ G (c : Circuit Basis.andOr2 N 1 G),
            G + 1 ≤ 2 ^ N / (5 * N) →
            (fun x => (c.eval x) 0) ≠ f

Here `G` is the number of internal gates and the output gate adds one more,
so `G + 1` is the total gate count (`Circuit.size` for a single-output circuit).

When `Basis.andOr2` is known to be complete, this yields a
`size_complexity` bound via `shannon_size_complexity`.
-/

/-- **Shannon lower bound in terms of `size_complexity`**: for `N ≥ 6`,
    there exists a Boolean function whose fan-in-2 AND/OR circuit complexity
    exceeds `2^N / (5N)`. -/
theorem shannon_size_complexity (N : Nat) [NeZero N] (hN : 6 ≤ N)
    [CompleteBasis Basis.andOr2] :
    ∃ f : BitString N → Bool,
      Circuit.size_complexity Basis.andOr2 f > 2 ^ N / (5 * N) := by
  obtain ⟨f, hf⟩ := shannon_lower_bound_circuit N hN
  refine ⟨f, ?_⟩
  by_contra hle; push_neg at hle
  obtain ⟨G, c, hs, hc⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) f
  have : c.size ≤ 2 ^ N / (5 * N) := hs ▸ hle
  exact hf G c (by rw [Circuit.size] at this; omega) hc

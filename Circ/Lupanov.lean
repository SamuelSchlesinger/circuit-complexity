import Circ.Shannon

/-! # Lupanov Upper Bound

Every Boolean function on `N` inputs can be computed by a fan-in-2 AND/OR
circuit with at most `C * 2^N / N` gates, for an explicit constant `C`.

This is the constructive complement to the Shannon counting lower bound:
Shannon shows some function requires `2^N / (5N)` gates, while Lupanov shows
no function needs more than `C * 2^N / N` gates, establishing that the
worst-case circuit complexity of Boolean functions is `Θ(2^N / N)`.

## Main results

* `lupanov_upper_bound` — for sufficiently large `N`, every Boolean function
  on `N` inputs has `size_complexity` at most `C * 2^N / N`.
-/

/-- **Lupanov upper bound**: there exists an explicit constant `C` such that
    for sufficiently large `N`, every Boolean function on `N` inputs can be
    computed by a fan-in-2 AND/OR circuit of size at most `C * 2^N / N`. -/
theorem lupanov_upper_bound [CompleteBasis Basis.andOr2] :
    ∃ C : Nat, ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ [NeZero N],
      ∀ f : BitString N → Bool,
        Circuit.size_complexity Basis.andOr2 f ≤ C * 2 ^ N / N := by
  sorry

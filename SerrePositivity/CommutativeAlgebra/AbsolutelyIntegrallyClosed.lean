module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# 絶対整閉な環

## 概要

可換環 `S` が絶対整閉であるとは、次数が正のモニック多項式がすべて `S` に根を持つことをいう。
Bhatt–Scholze, Thm 7.14 の用語である。
帰結として、任意の元が両立する `p` 冪根の系を持つことを示す（`exists_compatible_pow_roots`）。

## 規約と注意

原典は「任意のモニック多項式が解を持つ」と書くが、次数 0 のモニック多項式は `1` で根を持たない。
そのため、次数が正という条件を明示する。
零環では次数が正の多項式がないので、条件は自明に成り立つ。

## 使われ方

André の平坦性補題（`BhattScholze/Inputs/AndreFlatness.lean`）の主張と、
その帰結である `p` 冪根の存在に使う。
-/

@[expose] public section

open Polynomial

universe u

namespace SerrePositivity

/-- 環 `S` が絶対整閉であること。次数が正の任意のモニック多項式が `S` に根を持つ。
BS Thm 7.14 の用語で、André の平坦性補題が与える拡大の性質である。 -/
def IsAbsolutelyIntegrallyClosed (S : Type u) [CommRing S] : Prop :=
  ∀ P : S[X], P.Monic → 0 < P.natDegree → ∃ x : S, P.IsRoot x

/-- 絶対整閉な環では、任意の元 `a` が両立する `n` 乗根の系を持つ。すなわち
`r 0 = a` かつ各 `k` で `r (k+1) ^ n = r k` を満たす列 `r` がある。ただし `0 < n`。
各段で `X^n - r k` が次数 `n` のモニック多項式であることから、根を順に選ぶ。 -/
theorem IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots {S : Type u} [CommRing S]
    (hS : IsAbsolutelyIntegrallyClosed S) {n : ℕ} (hn : 0 < n) (a : S) :
    ∃ r : ℕ → S, r 0 = a ∧ ∀ k, r (k + 1) ^ n = r k := by
  have hroot : ∀ b : S, ∃ x : S, x ^ n = b := by
    intro b
    by_cases h1 : (1 : S) = 0
    · exact ⟨0, Subsingleton.elim (h := subsingleton_of_zero_eq_one h1.symm) _ _⟩
    have : Nontrivial S := ⟨⟨1, 0, h1⟩⟩
    obtain ⟨x, hx⟩ := hS (X ^ n - C b) (monic_X_pow_sub_C b hn.ne')
      (by rw [natDegree_X_pow_sub_C]; exact hn)
    exact ⟨x, by simpa [sub_eq_zero] using hx⟩
  choose root hroot using hroot
  refine ⟨fun k ↦ Nat.rec a (fun _ b ↦ root b) k, rfl, fun k ↦ hroot _⟩

end SerrePositivity

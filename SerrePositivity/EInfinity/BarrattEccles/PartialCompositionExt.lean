module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleChainMap

/-!
# Barratt–Eccles の二因子テンソルからの射の外延性

概要：Berger–Fresse §1.1.3 の部分合成の射の法則を負の斉次純粋テンソルで判定する。
方針：全テンソルの直和の外延性と加群テンソルの外延性を使い、正次数の零成分を除く。
規約：出力次数は −(p+q)、入力次数は −p,−q で調べれば足りる。
使われ方：部分合成の等変性と単位則を鎖次数で検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：二つの Barratt–Eccles 複体のテンソルからの射は負の純粋テンソルで決まる（Berger–Fresse §1.1.3）。
方針：各整数次数の直和成分を調べ、正次数の元を零にして残りを自然数の負号で表す。
規約：任意の出力のコチェイン複体に対して成立する。
使われ方：部分合成の射の等式を明示的な shuffle の等式へ帰着する。 -/
lemma tensor_complex_hom_ext (m n : ℕ) {T : Complex A}
    (f g : complex A m ⊗ complex A n ⟶ T)
    (h : ∀ (p q : ℕ) (x : (complex A m).X (-(p : ℤ)))
      (y : (complex A n).X (-(q : ℤ))),
      f.f (-((p + q : ℕ) : ℤ))
          (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ))
            (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)) =
        g.f (-((p + q : ℕ) : ℤ))
          (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ))
            (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y))) : f = g := by
  apply HomologicalComplex.hom_ext
  intro t
  apply mapBifunctor.hom_ext
  intro r s hrs
  change r + s = t at hrs
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change f.f t (ιTensorObj (complex A m) (complex A n) r s t hrs (x ⊗ₜ[A] y)) =
    g.f t (ιTensorObj (complex A m) (complex A n) r s t hrs (x ⊗ₜ[A] y))
  by_cases hr : 0 < r
  · have hx := complex_eq_zero_of_positive A m r hr x
    simp only [hx, TensorProduct.zero_tmul, map_zero]
  by_cases hs : 0 < s
  · have hy := complex_eq_zero_of_positive A n s hs y
    simp only [hy, TensorProduct.tmul_zero, map_zero]
  have ht : t ≤ 0 := by omega
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, r = -(p : ℤ) := ⟨(-r).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, s = -(q : ℤ) := ⟨(-s).toNat, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = -(k : ℤ) := ⟨(-t).toNat, by omega⟩
  have hk : p + q = k := by omega
  subst k
  exact h p q x y

end SerrePositivity.EInfinity.BarrattEccles

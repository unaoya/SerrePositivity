module

public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionExt
public import SerrePositivity.DifferentialGraded.Complexes.Braiding

/-!
# 三因子の Barratt–Eccles 複体の射の外延性

概要：Berger–Fresse §1.1.3 の結合則を負の斉次三重テンソルで判定する。
方針：三重全テンソルの外延性を使い、各入力の正次数成分を除く。
規約：中間次数は −(p+q)、最終次数は −(p+q+r) とする。
使われ方：shuffle の結合則を複体の射の等式へ移す。
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

/-- 概要：三因子からの複体の射は負の斉次純粋テンソルで決まる（Berger–Fresse §1.1.3）。
方針：三重テンソルの外延性と正次数成分の零性を使う。
規約：テンソルの括弧は左に置く。
使われ方：部分合成の二つの結合則を成分で検証する。 -/
lemma triple_complex_hom_ext (m n k : ℕ) {T : Complex A}
    (f g : (complex A m ⊗ complex A n) ⊗ complex A k ⟶ T)
    (h : ∀ (p q r : ℕ) (x : (complex A m).X (-(p : ℤ)))
      (y : (complex A n).X (-(q : ℤ))) (z : (complex A k).X (-(r : ℤ))),
      f.f (-((p + q + r : ℕ) : ℤ))
          (ιTensorObj (complex A m ⊗ complex A n) (complex A k)
            (-((p + q : ℕ) : ℤ)) (-(r : ℤ)) (-((p + q + r : ℕ) : ℤ)) (by omega)
            (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ))
              (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
        g.f (-((p + q + r : ℕ) : ℤ))
          (ιTensorObj (complex A m ⊗ complex A n) (complex A k)
            (-((p + q : ℕ) : ℤ)) (-(r : ℤ)) (-((p + q + r : ℕ) : ℤ)) (by omega)
            (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ))
              (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y) ⊗ₜ[A] z))) : f = g := by
  apply SerrePositivity.DifferentialGraded.triple_ext
  intro i j l t ht
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change f.f t (ιTensorObj (complex A m ⊗ complex A n) (complex A k) (i + j) l t ht
      (ιTensorObj (complex A m) (complex A n) i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    g.f t (ιTensorObj (complex A m ⊗ complex A n) (complex A k) (i + j) l t ht
      (ιTensorObj (complex A m) (complex A n) i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))
  by_cases hi : 0 < i
  · simp only [complex_eq_zero_of_positive A m i hi x, TensorProduct.zero_tmul, map_zero]
  by_cases hj : 0 < j
  · simp only [complex_eq_zero_of_positive A n j hj y, TensorProduct.tmul_zero,
      TensorProduct.zero_tmul, map_zero]
  by_cases hl : 0 < l
  · simp only [complex_eq_zero_of_positive A k l hl z, TensorProduct.tmul_zero, map_zero]
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, l = -(r : ℤ) := ⟨(-l).toNat, by omega⟩
  subst t
  have hv := h p q r x y z
  have hmid : -((p + q : ℕ) : ℤ) = -(p : ℤ) + -(q : ℤ) := by omega
  have hout : -((p + q + r : ℕ) : ℤ) = -(p : ℤ) + -(q : ℤ) + -(r : ℤ) := by omega
  have reindex (a b : ℤ) (ha : -((p + q : ℕ) : ℤ) = a)
      (hb : -((p + q + r : ℕ) : ℤ) = b) (hab : a + -(r : ℤ) = b)
      (hpq : -(p : ℤ) + -(q : ℤ) = a) :
      f.f b (ιTensorObj (complex A m ⊗ complex A n) (complex A k) a (-(r : ℤ)) b hab
        (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ)) a hpq
          (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      g.f b (ιTensorObj (complex A m ⊗ complex A n) (complex A k) a (-(r : ℤ)) b hab
        (ιTensorObj (complex A m) (complex A n) (-(p : ℤ)) (-(q : ℤ)) a hpq
          (x ⊗ₜ[A] y) ⊗ₜ[A] z)) := by
    subst a b
    exact hv
  exact reindex _ _ hmid hout (by omega) rfl

end SerrePositivity.EInfinity.BarrattEccles

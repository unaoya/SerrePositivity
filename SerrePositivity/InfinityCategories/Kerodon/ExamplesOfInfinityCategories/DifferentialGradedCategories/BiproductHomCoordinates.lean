module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Basic

/-! # 二項直和への Hom の全次数座標

概要：二項直和への斉次 cochain は二つの脚への cochain の組と A 線形に同値。
方針：直和の射影と包含の合成、二項直和の恒等射の分解を使う。
規約：HTT §1.2.13、HA Construction 1.3.1.6。使われ方：N7c の Hom-fiber の三成分表示。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] (X B C : Complex A)

/-- 概要：直和への Hom の全次数の A 線形座標。
方針：二射影との合成と二包含を用いた和を互いに逆とする。
規約：HTT §1.2.13。使われ方：標準 fiber の二つの脚の座標。 -/
def biproductHomCoordinates (n : ℤ) :
    Cochain X (B ⊞ C) n ≃ₗ[A] (Cochain X B n × Cochain X C n) where
  toFun a := (a.comp (Cochain.ofHom biprod.fst) (add_zero n),
    a.comp (Cochain.ofHom biprod.snd) (add_zero n))
  invFun a := a.1.comp (Cochain.ofHom biprod.inl) (add_zero n) +
    a.2.comp (Cochain.ofHom biprod.inr) (add_zero n)
  left_inv a := by
    dsimp only
    rw [Cochain.comp_assoc_of_second_is_zero_cochain,
      Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
      ← Cochain.comp_add, ← Cochain.ofHom_add, biprod.total, Cochain.comp_id]
  right_inv a := by
    apply Prod.ext
    · simp only [Cochain.add_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
        ← Cochain.ofHom_comp, biprod.inl_fst, biprod.inr_fst, Cochain.ofHom_zero,
        Cochain.comp_zero, add_zero, Cochain.comp_id]
    · simp only [Cochain.add_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
        ← Cochain.ofHom_comp, biprod.inl_snd, biprod.inr_snd, Cochain.ofHom_zero,
        Cochain.comp_zero, zero_add, Cochain.comp_id]
  map_add' a b := by
    apply Prod.ext <;> exact Cochain.add_comp _ _ _ (add_zero n)
  map_smul' c a := by
    apply Prod.ext <;> exact Cochain.smul_comp _ _ _ (add_zero n)

/-- 概要：直和 Hom の逆座標写像は二包含による和。
方針：線形同値の逆写像を評価する。
規約：HTT §1.2.13。使われ方：二つの脚からの斉次射の明示的な回収。 -/
lemma biproductHomCoordinates_symm (n : ℤ) (a : Cochain X B n × Cochain X C n) :
    (biproductHomCoordinates X B C n).symm a =
      a.1.comp (Cochain.ofHom biprod.inl) (add_zero n) +
        a.2.comp (Cochain.ofHom biprod.inr) (add_zero n) := rfl

/-- 概要：直和 Hom の逆座標写像は Hom 微分と可換。
方針：微分の和への分配と閉零の包含との合成の Leibniz 則を使う。
規約：HTT §1.2.13。使われ方：Hom-fiber の複体としての厳密な比較。 -/
lemma biproductHomCoordinates_symm_differential (n : ℤ) (a : Cochain X B n) (b : Cochain X C n) :
    δ n (n + 1) ((biproductHomCoordinates X B C n).symm (a, b)) =
      (biproductHomCoordinates X B C (n + 1)).symm (δ n (n + 1) a, δ n (n + 1) b) := by
  simp only [biproductHomCoordinates_symm, δ_add, δ_comp_zero_cochain,
    δ_ofHom, Cochain.comp_zero, zero_add]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

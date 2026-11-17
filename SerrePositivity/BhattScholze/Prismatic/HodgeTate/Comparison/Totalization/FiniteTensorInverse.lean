module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteTensorComparison

/-!
# 有限頭部のテンソル比較の両逆

## 概要
有限個の指定行を戻す射が、標準の次数ごとの比較の両逆となることを確認する。

## 方針
同じ行の射影は恒等、異なる行の射影は零となる行列の式と、元の有限成分展開を使う。

## 規約
内部次数の有界性や係数の有限性は要求しない。横次数の高い行の零性だけを使う。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部の標準比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped TensorProduct BigOperators

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 指定行を戻した後の同じ行の比較成分は、元の行の恒等射。 -/
theorem tensorInsertRow_comparison_self (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (q : ℤ) (n : ℕ) :
    tensorInsertRow L K q n ≫ tensorComparisonDegree L K q ≫ componentπ (tensorRows L K) n q = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro a t hat
  change a+t=q-n at hat
  have ht : t = (q-a)-n := by omega
  subst t
  erw [Category.comp_id]
  rw [ι_tensorInsertRow_assoc]
  simp only [tensorInsertSummand, eqToHom_refl, Category.id_comp]
  rw [Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [tensorComparisonDegree_component]
  dsimp only [tensorComponent]
  rw [Linear.comp_units_smul]
  simp only [interchangeSign, smul_smul, Int.units_mul_self, one_smul]
  rw [← Category.assoc, ← whiskerLeft_comp, insertMorphism_component_self]
  simp only [whiskerLeft_id, Category.id_comp]

/-- 指定行を戻した後の異なる行の比較成分は零。 -/
theorem tensorInsertRow_comparison_ne (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (q : ℤ) (n m : ℕ) (h : m ≠ n) :
    tensorInsertRow L K q n ≫ tensorComparisonDegree L K q ≫ componentπ (tensorRows L K) m q = 0 := by
  apply mapBifunctor.hom_ext
  intro a t hat
  change a+t=q-n at hat
  have ht : t = (q-a)-n := by omega
  subst t
  simp only [Category.assoc, comp_zero]
  rw [ι_tensorInsertRow_assoc]
  simp only [tensorInsertSummand, eqToHom_refl, Category.id_comp]
  rw [Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [tensorComparisonDegree_component]
  dsimp only [tensorComponent]
  rw [Linear.comp_units_smul, ← Category.assoc, ← whiskerLeft_comp,
    insertMorphism_component_ne K (q-a) n m h]
  simp only [MonoidalPreadditive.whiskerLeft_zero, zero_comp, smul_zero]

/-- 逆の有限和の後の標準比較は、有限頭部の指定 Tot の恒等射。 -/
theorem finiteTensorInverse_comp_comparison (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (N : ℕ) (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n)) (q : ℤ) :
    finiteTensorInverseDegree L K N q ≫ tensorComparisonDegree L K q = 𝟙 _ := by
  apply component_hom_ext
  intro m
  by_cases hm : m < N
  · simp only [finiteTensorInverseDegree, Preadditive.sum_comp, Category.assoc, Category.id_comp]
    rw [Finset.sum_eq_single m]
    · rw [tensorInsertRow_comparison_self, Category.comp_id]
    · intro n hn hnm
      rw [tensorInsertRow_comparison_ne L K q n m (Ne.symm hnm), comp_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hm))
  · have hz := (cochainTensorFixedLeft L).map_isZero (hK m (by omega))
    exact ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) (q-m)).map_isZero hz).eq_of_tgt _ _

/-- 有限成分展開を、同じ Tot の次数ごとの恒等射として使う。 -/
theorem finite_component_identity (K : CochainComplex (Complex R) ℕ)
    (N : ℕ) (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n)) (q : ℤ) :
    (∑ n ∈ Finset.range N, componentπ K n q ≫ insertMorphism K q n) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, insertMorphism_apply, ModuleCat.hom_id, LinearMap.id_apply] using
      (finite_component_expansion K N hK q x).symm

/-- 比較で一行へ移した同次テンソルを戻すと、元の同次テンソルのその行の成分となる。 -/
theorem tensorComponent_insertRow (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (a b q : ℤ) (hab : a+b=q) (n : ℕ) :
    tensorComponent L K a b q hab n ≫ tensorInsertRow L K q n =
      (L.X a ◁ (componentπ K n b ≫ insertMorphism K b n)) ≫
        ιTensorObj L (total K) a b q hab := by
  have hb : b = q-a := by omega
  subst b
  dsimp only [tensorComponent]
  rw [Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [ι_tensorInsertRow]
  simp only [tensorInsertSummand, eqToHom_refl, Category.id_comp]
  rw [Linear.comp_units_smul]
  simp only [interchangeSign, smul_smul, Int.units_mul_self, one_smul]
  rw [← Category.assoc, ← whiskerLeft_comp]

/-- 標準比較の後の逆の有限和は、元のテンソルの恒等射。 -/
theorem comparison_comp_finiteTensorInverse (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (N : ℕ) (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n)) (q : ℤ) :
    tensorComparisonDegree L K q ≫ finiteTensorInverseDegree L K N q = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro a b hab
  simp only [finiteTensorInverseDegree, Preadditive.comp_sum, Category.assoc, Category.comp_id]
  simp_rw [tensorComparisonDegree_component_assoc, tensorComponent_insertRow]
  rw [← Preadditive.sum_comp, ← whiskerLeft_sum, finite_component_identity K N hK b]
  simp only [whiskerLeft_id, Category.id_comp]

/-- 有限頭部の標準の次数比較は、元の挿入からなる逆を持つ同型。 -/
def finiteTensorComparisonDegreeIso (L : Complex R) (K : CochainComplex (Complex R) ℕ)
    (N : ℕ) (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n)) (q : ℤ) :
    (cochainTensor L (total K)).X q ≅ (total (tensorRows L K)).X q where
  hom := tensorComparisonDegree L K q
  inv := finiteTensorInverseDegree L K N q
  hom_inv_id := comparison_comp_finiteTensorInverse L K N hK q
  inv_hom_id := finiteTensorInverse_comp_comparison L K N hK q

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

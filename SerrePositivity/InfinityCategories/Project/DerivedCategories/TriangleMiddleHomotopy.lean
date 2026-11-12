module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TriangleMiddleMissingFace
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangleMiddlePrism
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! # 三角形の中間対象を変える実際のホモトピー

概要：中間対象の因子分解は両端と対角を保つ単体的ホモトピーを与える。
方針：三角柱から中間対象比較三単体への写像を使い、各面の式を適用する。
規約：次数 −1 のホモトピーを保持する。使われ方：D7 の四角形の比較の下側セル。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (a : A ⟶ B) (m : B ⟶ C) (b : C ⟶ D) (c : A ⟶ D) (t : Cochain A D (-1))
variable (ht : δ (-1) 0 t = Cochain.ofHom ((a ≫ m) ≫ b) - Cochain.ofHom c)

/-- 中間対象の因子分解の実際の三角形ホモトピー。 -/
def complexTriangleMiddleHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a (m ≫ b) c t (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_sourceEquation a m b c t ht)).simplex)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (a ≫ m) b c t ht).simplex) where
  h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle a m b c t ht)
  h₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_zero,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_face_two a m b c t ht)
  h₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_one,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_face_one a m b c t ht)
  rel := by
    ext n s
    exact False.elim s.1.2

/-- 中間対象比較のホモトピーは対角を全パラメーターで固定する。 -/
lemma complexTriangleMiddleHomotopy_diagonal :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (complexTriangleMiddleHomotopy a m b c t ht).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a (m ≫ b) c t
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_sourceEquation a m b c t ht)).simplex := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ≫ _) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_diagonal, Category.assoc, Category.assoc,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg (fun z => CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
    SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_face_two a m b c t ht)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTriangleMiddleMissingFace
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
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
variable {W X Y Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
variable (a : W ⟶ X) (m : X ⟶ Y) (b : Y ⟶ Z) (c : W ⟶ Z)
variable (t : _root_.SerrePositivity.DifferentialGraded.GradedHom R (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Z) (-1))
variable (ht : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Z)).d (-1) 0 t =
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) ((a ≫ m) ≫ b))).val -
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) c)).val)

/-- 中間対象の因子分解の実際の三角形ホモトピー。 -/
def dgModuleTriangleMiddleHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D a (m ≫ b) c t
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddle_sourceEquation R D a m b c t ht)).simplex)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D (a ≫ m) b c t ht).simplex) where
  h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddle R D a m b c t ht)
  h₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_zero,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddle_face_two R D a m b c t ht)
  h₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_one,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddle_face_one R D a m b c t ht)
  rel := by
    ext n s
    exact False.elim s.1.2

/-- 中間対象比較のホモトピーは対角を全パラメーターで固定する。 -/
lemma dgModuleTriangleMiddleHomotopy_diagonal :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (dgModuleTriangleMiddleHomotopy R D a m b c t ht).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D a (m ≫ b) c t
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddle_sourceEquation R D a m b c t ht)).simplex := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ≫ _) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_diagonal, Category.assoc, Category.assoc,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg (fun z => CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
    SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddle_face_two R D a m b c t ht)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleMiddleMissingFace
public import SerrePositivity.InfinityCategories.Stable.TriangleMiddlePrism
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {W X Y Z : ModuleCategory R D}
variable (a : W ⟶ X) (m : X ⟶ Y) (b : Y ⟶ Z) (c : W ⟶ Z)
variable (t : GradedHom R (ForgetEnrichment.to (Complex R) W)
  (ForgetEnrichment.to (Complex R) Z) (-1))
variable (ht : (moduleHom R D (ForgetEnrichment.to (Complex R) W)
  (ForgetEnrichment.to (Complex R) Z)).d (-1) 0 t =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) ((a ≫ m) ≫ b))).val -
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) c)).val)

/-- 中間対象の因子分解の実際の三角形ホモトピー。 -/
def dgModuleTriangleMiddleHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm
      (dgModuleCompStruct R D a (m ≫ b) c t
        (dgModuleTriangleMiddle_sourceEquation R D a m b c t ht)).simplex)
    (SSet.yonedaEquiv.symm (dgModuleCompStruct R D (a ≫ m) b c t ht).simplex) where
  h := triangleMiddlePrism ≫ SSet.yonedaEquiv.symm (dgModuleTriangleMiddle R D a m b c t ht)
  h₀ := by
    rw [← Category.assoc, triangleMiddlePrism_zero,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (dgModuleTriangleMiddle_face_two R D a m b c t ht)
  h₁ := by
    rw [← Category.assoc, triangleMiddlePrism_one,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (dgModuleTriangleMiddle_face_one R D a m b c t ht)
  rel := by
    ext n s
    exact False.elim s.1.2

/-- 中間対象比較のホモトピーは対角を全パラメーターで固定する。 -/
lemma dgModuleTriangleMiddleHomotopy_diagonal :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (dgModuleTriangleMiddleHomotopy R D a m b c t ht).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
          (dgModuleCompStruct R D a (m ≫ b) c t
            (dgModuleTriangleMiddle_sourceEquation R D a m b c t ht)).simplex := by
  change _ ≫ (triangleMiddlePrism ≫ _) = _
  rw [← Category.assoc, triangleMiddlePrism_diagonal, Category.assoc, Category.assoc,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg (fun z => CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
    SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm z)
      (dgModuleTriangleMiddle_face_two R D a m b c t ht)

end SerrePositivity.InfinityCategories

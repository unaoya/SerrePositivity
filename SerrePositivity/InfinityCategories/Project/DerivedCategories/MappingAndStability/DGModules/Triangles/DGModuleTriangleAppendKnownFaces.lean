module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGModuleTriangleAppendHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.TetrahedronFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 後合成比較三単体の既知面と最上位成分

概要：比較三単体の面 0・1・3 と最上位成分の零を公開する。
方針：ホーンの各面の保存と既存の零最上位充填の定義を使う。
規約：面 2 の同定には最上位方程式を使う。使われ方：β3 の双対比較。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 零面は中間射と後合成射の厳密三角形。 -/
lemma dgModuleTriangleAppend_face_zero (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle A D b q).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face A D a b c t ht q 0 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)
/-- 一面は対角射と後合成射の厳密三角形。 -/
lemma dgModuleTriangleAppend_face_one (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle A D c q).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face A D a b c t ht q 1 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)
/-- 三面は元の三角形。 -/
lemma dgModuleTriangleAppend_face_three (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face A D a b c t ht q 3 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)
/-- 比較三単体の最上位 cochain は零。 -/
lemma dgModuleTriangleAppend_top_zero (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q).hom Finset.univ 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData_top_zero _ _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

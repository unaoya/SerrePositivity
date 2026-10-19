module
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleMiddleHorn
public import SerrePositivity.InfinityCategories.Derived.TriangleMiddleKnownFaces
public import SerrePositivity.InfinityCategories.Derived.TetrahedronFaces
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-! # 中間対象比較三単体の指定面と零成分

概要：中間対象の因子分解比較の三つの指定面と最上位成分を計算する。
方針：内部ホーンの零最上位充填と三単体の方程式を使う。
規約：零の隣接ホモトピーなら対角を挟む二つのホモトピーが等しい。
使われ方：D7 の中間対象比較の欠けた面の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {W X Y Z : ModuleCategory R D}
variable (a : W ⟶ X) (m : X ⟶ Y) (b : Y ⟶ Z) (c : W ⟶ Z)
variable (t : GradedHom R (ForgetEnrichment.to (Complex R) W)
  (ForgetEnrichment.to (Complex R) Z) (-1))
variable (ht : (moduleHom R D (ForgetEnrichment.to (Complex R) W)
  (ForgetEnrichment.to (Complex R) Z)).d (-1) 0 t =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) ((a ≫ m) ≫ b))).val -
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) c)).val)

/-- 面 0 は後ろの二射の厳密三角形。 -/
lemma dgModuleTriangleMiddle_face_zero :
    (dgModuleTriangleMiddle R D a m b c t ht).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (strictDGModuleTriangle R D m b).simplex :=
  (dgModuleTriangleMiddle_face R D a m b c t ht 0 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

/-- 面 1 は中間対象を変更した三角形。 -/
lemma dgModuleTriangleMiddle_face_one :
    (dgModuleTriangleMiddle R D a m b c t ht).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (dgModuleCompStruct R D (a ≫ m) b c t ht).simplex :=
  (dgModuleTriangleMiddle_face R D a m b c t ht 1 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

/-- 面 3 は前の二射の厳密三角形。 -/
lemma dgModuleTriangleMiddle_face_three :
    (dgModuleTriangleMiddle R D a m b c t ht).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (strictDGModuleTriangle R D a m).simplex :=
  (dgModuleTriangleMiddle_face R D a m b c t ht 3 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

/-- 中間対象比較三単体の最上位 cochain は零。 -/
lemma dgModuleTriangleMiddle_top_zero :
    (dgModuleTriangleMiddle R D a m b c t ht).hom Finset.univ 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 :=
  HornData.fillerData_top_zero _ _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories

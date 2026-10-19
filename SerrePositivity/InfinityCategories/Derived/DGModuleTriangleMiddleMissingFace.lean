module
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleMiddleKnownFaces

/-! # 中間対象比較の欠けた面の同定

概要：零最上位充填の面 2 は元の中間対象を経由する三角形。
方針：指定面から各辺を回収し、三単体方程式で三点ホモトピーを同定する。
規約：二つの面は同じ次数 −1 cochain を保持する。使われ方：D7 の三角形のホモトピー。
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

include ht

/-- 因子分解前の中間対象を経由する三角形の微分式。 -/
lemma dgModuleTriangleMiddle_sourceEquation :
    (moduleHom R D (ForgetEnrichment.to (Complex R) W)
  (ForgetEnrichment.to (Complex R) Z)).d (-1) 0 t =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (a ≫ (m ≫ b)))).val -
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) c)).val := by
  simpa only [Category.assoc] using ht

/-- 面 2 は因子分解前の三角形とホモトピーを厳密に保つ。 -/
lemma dgModuleTriangleMiddle_face_two :
    (dgModuleTriangleMiddle R D a m b c t ht).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (dgModuleCompStruct R D a (m ≫ b) c t
        (dgModuleTriangleMiddle_sourceEquation R D a m b c t ht)).simplex := by
  let σ := dgModuleTriangleMiddle R D a m b c t ht
  have h0 := dgModuleTriangleMiddle_face_zero R D a m b c t ht
  have h1 := dgModuleTriangleMiddle_face_one R D a m b c t ht
  have h3 := dgModuleTriangleMiddle_face_three R D a m b c t ht
  have hx0 : σ.obj 0 = ForgetEnrichment.to (Complex R) W := dgTetrahedron_face_obj σ 1 _ h1 0
  have hx1 : σ.obj 1 = ForgetEnrichment.to (Complex R) X := dgTetrahedron_face_obj σ 3 _ h3 1
  have hx2 : σ.obj 2 = ForgetEnrichment.to (Complex R) Y := dgTetrahedron_face_obj σ 1 _ h1 1
  have hx3 : σ.obj 3 = ForgetEnrichment.to (Complex R) Z := dgTetrahedron_face_obj σ 1 _ h1 2
  have he01 : HEq (σ.toSimplexData.edgeHom 0 1 (by decide))
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a)).val) :=
    dgTetrahedron_face_edge σ 3 _ h3 0 1 (by decide)
  have he13 : HEq (σ.toSimplexData.edgeHom 1 3 (by decide))
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (m ≫ b))).val) :=
    dgTetrahedron_face_edge σ 0 _ h0 0 2 (by decide)
  have he03 : HEq (σ.toSimplexData.edgeHom 0 3 (by decide))
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) c)).val) :=
    dgTetrahedron_face_edge σ 1 _ h1 0 2 (by decide)
  have ht012 : HEq (σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide))
      (0 : GradedHom R (ForgetEnrichment.to (Complex R) W)
        (ForgetEnrichment.to (Complex R) Y) (-1)) := dgTetrahedron_face_triple σ 3 _ h3
  have ht123 : HEq (σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide))
      (0 : GradedHom R (ForgetEnrichment.to (Complex R) X)
        (ForgetEnrichment.to (Complex R) Z) (-1)) := dgTetrahedron_face_triple σ 0 _ h0
  have ht023 : HEq (σ.toSimplexData.tripleHom 0 2 3 (by decide) (by decide)) t :=
    dgTetrahedron_face_triple σ 1 _ h1
  have hz012 : σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) = 0 :=
    eq_of_heq (ht012.trans (gradedHom_zero_heq (A := R) (D := RightModule R D)
      (k := (-1)) (l := (-1)) hx0 hx2 rfl).symm)
  have hz123 : σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide) = 0 :=
    eq_of_heq (ht123.trans (gradedHom_zero_heq (A := R) (D := RightModule R D)
      (k := (-1)) (l := (-1)) hx1 hx3 rfl).symm)
  have ht013 := (heq_of_eq (dgTetrahedron_middle_triple σ
    (dgModuleTriangleMiddle_top_zero R D a m b c t ht) hz012 hz123)).trans ht023
  apply dgSimplex2_ext
  · funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx3
  · exact (dgTetrahedron_face_edge σ 2 _ rfl 0 1 (by decide)).symm.trans he01
  · exact (dgTetrahedron_face_edge σ 2 _ rfl 1 2 (by decide)).symm.trans he13
  · exact (dgTetrahedron_face_edge σ 2 _ rfl 0 2 (by decide)).symm.trans he03
  · exact (dgTetrahedron_face_triple σ 2 _ rfl).symm.trans ht013

end SerrePositivity.InfinityCategories

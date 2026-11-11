module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleTriangleAppendKnownFaces

/-! # 後合成比較三単体の欠けた面

概要：三次内部ホーンの零最上位充填の面 2 は、元の三角形を後合成した三角形である。
方針：既知面から辺・ホモトピーを回収し、最上位方程式で残る三点成分を決める。
規約：実際の二単体の等式。使われ方：β3 の双対比較の終点面。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 比較三単体の面 2 は元の三角形への後合成。 -/
lemma dgModuleTriangleAppend_face_two (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeDGModuleTriangle A D a b c t ht q := by
  let σ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_zero A D a b c t ht q
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_one A D a b c t ht q
  have h3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_three A D a b c t ht q
  have hx0 : σ.obj 0 = ForgetEnrichment.to (Complex A) W :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_obj σ 3 _ h3 0
  have hx1 : σ.obj 1 = ForgetEnrichment.to (Complex A) X :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_obj σ 3 _ h3 1
  have hx2 : σ.obj 2 = ForgetEnrichment.to (Complex A) Y :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_obj σ 3 _ h3 2
  have hx3 : σ.obj 3 = ForgetEnrichment.to (Complex A) Z :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_obj σ 0 _ h0 2
  have he01 : HEq (σ.toSimplexData.edgeHom 0 1 (by decide))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) a)).val :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 3 _ h3 0 1 (by decide)
  have he13 : HEq (σ.toSimplexData.edgeHom 1 3 (by decide))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (b ≫ q))).val :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 0 _ h0 0 2 (by decide)
  have he03 : HEq (σ.toSimplexData.edgeHom 0 3 (by decide))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (c ≫ q))).val :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 1 _ h1 0 2 (by decide)
  have he23 : HEq (σ.toSimplexData.edgeHom 2 3 (by decide))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).val :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 0 _ h0 1 2 (by decide)
  have ht012 : HEq (σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide)) t :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_triple σ 3 _ h3
  have ht023 : HEq (σ.toSimplexData.tripleHom 0 2 3 (by decide) (by decide))
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) W)
        (ForgetEnrichment.to (Complex A) Z) (-1)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_triple σ 1 _ h1
  have ht123 : HEq (σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide))
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) X)
        (ForgetEnrichment.to (Complex A) Z) (-1)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_triple σ 0 _ h0
  have hz023 : σ.toSimplexData.tripleHom 0 2 3 (by decide) (by decide) = 0 :=
    eq_of_heq (ht023.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (D := RightModule A D)
      (k := (-1)) (l := (-1)) hx0 hx3 rfl).symm)
  have hz123 : σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide) = 0 :=
    eq_of_heq (ht123.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (D := RightModule A D)
      (k := (-1)) (l := (-1)) hx1 hx3 rfl).symm)
  have hmiss := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_missing_triple σ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_top_zero A D a b c t ht q)
    hz023 hz123
  have ht013 : HEq (σ.toSimplexData.tripleHom 0 1 3 (by decide) (by decide))
      (compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).val t
        (add_zero (-1))) := by
    apply (heq_of_eq hmiss).trans
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) (D := RightModule A D) hx0 hx2 hx3 rfl rfl rfl
      _ _ (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) q)).val t he23 ht012
      (add_zero (-1)) (add_zero (-1)))
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx3
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 2 _ rfl 0 1 (by decide)).symm.trans he01
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 2 _ rfl 1 2 (by decide)).symm.trans he13
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 2 _ rfl 0 2 (by decide)).symm.trans he03
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_triple σ 2 _ rfl).symm.trans ht013

end SerrePositivity.InfinityCategories.Project.DerivedCategories

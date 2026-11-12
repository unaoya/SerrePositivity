module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TriangleAppendHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TetrahedronFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 後合成比較三単体の既知面と最上位成分

概要：比較三単体の面 0・1・3 と最上位成分の零を公開する。
方針：ホーンの各面の保存と既存の零最上位充填の定義を使う。
規約：面 2 の同定には最上位方程式を使う。使われ方：D7 の双対比較。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
variable {S : Type u} [CommRing S] {W X Y Z : Complex S}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 零面は中間射と後合成射の厳密三角形。 -/
lemma complexTriangleAppend_face_zero (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y) (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend a b c t ht q).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle b q).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face a b c t ht q 0 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)
/-- 一面は対角射と後合成射の厳密三角形。 -/
lemma complexTriangleAppend_face_one (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y) (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend a b c t ht q).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle c q).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face a b c t ht q 1 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)
/-- 三面は元の三角形。 -/
lemma complexTriangleAppend_face_three (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y) (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend a b c t ht q).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a b c t ht).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face a b c t ht q 3 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)
/-- 比較三単体の最上位 cochain は零。 -/
lemma complexTriangleAppend_top_zero (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y) (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend a b c t ht q).hom Finset.univ 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData_top_zero _ _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

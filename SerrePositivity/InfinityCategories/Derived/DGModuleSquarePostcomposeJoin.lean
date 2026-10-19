module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Derived.SpanJoinFaces

/-! # 四角形の終点への後合成を表す join

概要：終点だけを後合成する四角形の比較を span⋆Δ¹ 上の写像として構成する。
方針：上下の後合成比較三単体を共通面に沿って貼る。
規約：両端の四角形と共通の span を厳密に保持する。使われ方：D7 の suspension 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Z T : ModuleCategory A D}
variable (s : DGModuleSquareData A D W X Y Z) (q : Z ⟶ T)

/-- 下側三角形への後合成を表す比較三単体。 -/
def postcomposeLower : Simplex A (RightModule A D) 3 :=
  dgModuleTriangleAppend A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation q

/-- 上側三角形への後合成を表す比較三単体。 -/
def postcomposeUpper : Simplex A (RightModule A D) 3 :=
  dgModuleTriangleAppend A D s.left s.top s.diagonal s.upperHomotopy s.upperEquation q

/-- lower 比較の面 3。 -/
lemma postcomposeLower_face_three :
    (s.postcomposeLower q).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      s.lowerTriangle :=
  dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

/-- lower 比較の面 2。 -/
lemma postcomposeLower_face_two :
    (s.postcomposeLower q).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (s.postcompose q).lowerTriangle :=
  dgModuleTriangleAppend_face_two A D _ _ _ _ _ _

/-- upper 比較の面 3。 -/
lemma postcomposeUpper_face_three :
    (s.postcomposeUpper q).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      s.upperTriangle :=
  dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

/-- upper 比較の面 2。 -/
lemma postcomposeUpper_face_two :
    (s.postcomposeUpper q).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (s.postcompose q).upperTriangle :=
  dgModuleTriangleAppend_face_two A D _ _ _ _ _ _

/-- 二つの比較三単体は対角と q の面で一致する。 -/
lemma postcomposeCells_compatible :
    SSet.stdSimplex.δ (1 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (s.postcomposeLower q) :
          (Δ[3] : SSet.{max (u + 1) v}) ⟶ dgModuleNerve A D) =
      SSet.stdSimplex.δ (1 : Fin 4) ≫ SSet.yonedaEquiv.symm (s.postcomposeUpper q) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    ((dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).trans
      (dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).symm)

/-- Span を固定する後合成比較の join 写像。 -/
def postcomposeJoin : join (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ⟶ dgModuleNerve A D :=
  (spanJoin_isPushout 1).desc (SSet.yonedaEquiv.symm (s.postcomposeLower q))
    (SSet.yonedaEquiv.symm (s.postcomposeUpper q)) (s.postcomposeCells_compatible q)

/-- 左セルへの制限。 -/
lemma postcomposeJoin_left : spanJoinLeft 1 ≫ s.postcomposeJoin q =
    SSet.yonedaEquiv.symm (s.postcomposeLower q) :=
  (spanJoin_isPushout 1).inl_desc _ _ _

/-- 右セルへの制限。 -/
lemma postcomposeJoin_right : spanJoinRight 1 ≫ s.postcomposeJoin q =
    SSet.yonedaEquiv.symm (s.postcomposeUpper q) :=
  (spanJoin_isPushout 1).inr_desc _ _ _

/-- 比較の始点は元の四角形の余錐。 -/
lemma postcomposeJoin_face_one :
    joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      s.postcomposeJoin q = (pushoutCocone s.square).val := by
  apply (spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← spanJoinLeft_face, Category.assoc,
      postcomposeJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeLower q).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ dgModuleNerve A D) = _
    rw [postcomposeLower_face_three]
    change _ = spanCoconeTriangleLeft ≫ (spanCoconeSquareIso.hom ≫ s.square)
    rw [← Category.assoc, spanCoconeSquareIso_left, square_lower]
  · rw [← Category.assoc, ← spanJoinRight_face, Category.assoc,
      postcomposeJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeUpper q).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ dgModuleNerve A D) = _
    rw [postcomposeUpper_face_three]
    change _ = spanCoconeTriangleRight ≫ (spanCoconeSquareIso.hom ≫ s.square)
    rw [← Category.assoc, spanCoconeSquareIso_right, square_upper]

/-- 比較の終点は後合成した四角形の余錐。 -/
lemma postcomposeJoin_face_zero :
    joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      s.postcomposeJoin q = (pushoutCocone (s.postcompose q).square).val := by
  apply (spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← spanJoinLeft_face, Category.assoc,
      postcomposeJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeLower q).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ dgModuleNerve A D) = _
    rw [postcomposeLower_face_two]
    change _ = spanCoconeTriangleLeft ≫ (spanCoconeSquareIso.hom ≫ (s.postcompose q).square)
    rw [← Category.assoc, spanCoconeSquareIso_left, square_lower]
  · rw [← Category.assoc, ← spanJoinRight_face, Category.assoc,
      postcomposeJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeUpper q).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ dgModuleNerve A D) = _
    rw [postcomposeUpper_face_two]
    change _ = spanCoconeTriangleRight ≫ (spanCoconeSquareIso.hom ≫ (s.postcompose q).square)
    rw [← Category.assoc, spanCoconeSquareIso_right, square_upper]

end SerrePositivity.InfinityCategories.DGModuleSquareData

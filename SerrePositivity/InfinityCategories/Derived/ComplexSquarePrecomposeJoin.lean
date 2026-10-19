module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquarePrecomposeData
public import SerrePositivity.InfinityCategories.DGNerve.CospanJoinCells
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryTriangles

/-! # 四角形の始点への前合成を表す join

概要：始点だけを前合成する四角形の比較を Δ¹⋆cospan 上に構成する。
方針：上下の prepend 比較三単体を対角の共通面に沿って貼る。
規約：両端の四角形と共通の cospan を保つ。使われ方：D7 の suspension 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.ComplexSquareData
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {V A B C D : Complex S}
variable (s : ComplexSquareData A B C D) (p : V ⟶ A)

/-- 前合成比較の二セルは対角で一致する。 -/
lemma precomposeCells_compatible :
    SSet.stdSimplex.δ (2 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (s.precomposeLower p) :
          (Δ[3] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (2 : Fin 4) ≫ SSet.yonedaEquiv.symm (s.precomposeUpper p) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (s.precompose_common p)

/-- Cospan を固定する前合成比較の join 写像。 -/
def precomposeJoin : join (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ⟶ dgNerve S (Complex S) :=
  (cospanJoin_isPushout 1).desc (SSet.yonedaEquiv.symm (s.precomposeLower p))
    (SSet.yonedaEquiv.symm (s.precomposeUpper p)) (s.precomposeCells_compatible p)

/-- 左セルへの制限。 -/
lemma precomposeJoin_left : cospanJoinLeft 1 ≫ s.precomposeJoin p =
    SSet.yonedaEquiv.symm (s.precomposeLower p) :=
  (cospanJoin_isPushout 1).inl_desc _ _ _

/-- 右セルへの制限。 -/
lemma precomposeJoin_right : cospanJoinRight 1 ≫ s.precomposeJoin p =
    SSet.yonedaEquiv.symm (s.precomposeUpper p) :=
  (cospanJoin_isPushout 1).inr_desc _ _ _

/-- 比較の終点は元の四角形の錐。 -/
lemma precomposeJoin_face_zero :
    joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫
      s.precomposeJoin p = (pullbackCone s.square).val := by
  apply (cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc,
      precomposeJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.precomposeLower p).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [precomposeLower_face_zero]
    change _ = cospanConeTriangleLeft ≫ (cospanConeSquareIso.hom ≫ s.square)
    rw [← Category.assoc, cospanConeSquareIso_left, square_lower]
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc,
      precomposeJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.precomposeUpper p).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [precomposeUpper_face_zero]
    change _ = cospanConeTriangleRight ≫ (cospanConeSquareIso.hom ≫ s.square)
    rw [← Category.assoc, cospanConeSquareIso_right, square_upper]

/-- 比較の始点は前合成した四角形の錐。 -/
lemma precomposeJoin_face_one :
    joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫
      s.precomposeJoin p = (pullbackCone (s.precompose p).square).val := by
  apply (cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc,
      precomposeJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.precomposeLower p).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [precomposeLower_face_one]
    change _ = cospanConeTriangleLeft ≫ (cospanConeSquareIso.hom ≫ (s.precompose p).square)
    rw [← Category.assoc, cospanConeSquareIso_left, square_lower]
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc,
      precomposeJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.precomposeUpper p).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) = _
    rw [precomposeUpper_face_one]
    change _ = cospanConeTriangleRight ≫ (cospanConeSquareIso.hom ≫ (s.precompose p).square)
    rw [← Category.assoc, cospanConeSquareIso_right, square_upper]

end SerrePositivity.InfinityCategories.ComplexSquareData

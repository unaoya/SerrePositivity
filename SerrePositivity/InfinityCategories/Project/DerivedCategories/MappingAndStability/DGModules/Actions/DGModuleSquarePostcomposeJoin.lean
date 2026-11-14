module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanJoinFaces

/-! # 四角形の終点への後合成を表す join

概要：終点だけを後合成する四角形の比較を span⋆Δ¹ 上の写像として構成する。
方針：上下の後合成比較三単体を共通面に沿って貼る。
規約：両端の四角形と共通の span を厳密に保持する。使われ方：D7 の suspension 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Z T : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y Z) (q : Z ⟶ T)

/-- 下側三角形への後合成を表す比較三単体。 -/
def postcomposeLower : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation q

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeLower)


/-- 上側三角形への後合成を表す比較三単体。 -/
def postcomposeUpper : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D s.left s.top s.diagonal s.upperHomotopy s.upperEquation q

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeUpper)


/-- lower 比較の面 3。 -/
lemma postcomposeLower_face_three :
    (s.postcomposeLower q).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      s.lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeLower_face_three)


/-- lower 比較の面 2。 -/
lemma postcomposeLower_face_two :
    (s.postcomposeLower q).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (s.postcompose q).lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_two A D _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeLower_face_two)


/-- upper 比較の面 3。 -/
lemma postcomposeUpper_face_three :
    (s.postcomposeUpper q).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      s.upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_three A D _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeUpper_face_three)


/-- upper 比較の面 2。 -/
lemma postcomposeUpper_face_two :
    (s.postcomposeUpper q).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (s.postcompose q).upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_two A D _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeUpper_face_two)


/-- 二つの比較三単体は対角と q の面で一致する。 -/
lemma postcomposeCells_compatible :
    SSet.stdSimplex.δ (1 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (s.postcomposeLower q) :
          (Δ[3] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) =
      SSet.stdSimplex.δ (1 : Fin 4) ≫ SSet.yonedaEquiv.symm (s.postcomposeUpper q) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_one A D _ _ _ _ _ _).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeCells_compatible)


/-- Span を固定する後合成比較の join 写像。 -/
def postcomposeJoin : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).desc (SSet.yonedaEquiv.symm (s.postcomposeLower q))
    (SSet.yonedaEquiv.symm (s.postcomposeUpper q)) (s.postcomposeCells_compatible q)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeJoin)


/-- 左セルへの制限。 -/
lemma postcomposeJoin_left : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft 1 ≫ s.postcomposeJoin q =
    SSet.yonedaEquiv.symm (s.postcomposeLower q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).inl_desc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeJoin_left)


/-- 右セルへの制限。 -/
lemma postcomposeJoin_right : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight 1 ≫ s.postcomposeJoin q =
    SSet.yonedaEquiv.symm (s.postcomposeUpper q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).inr_desc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeJoin_right)


/-- 比較の始点は元の四角形の余錐。 -/
lemma postcomposeJoin_face_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      s.postcomposeJoin q = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, Category.assoc,
      postcomposeJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeLower q).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [postcomposeLower_face_three]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ s.square)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, Category.assoc,
      postcomposeJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeUpper q).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [postcomposeUpper_face_three]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ s.square)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeJoin_face_one)


/-- 比較の終点は後合成した四角形の余錐。 -/
lemma postcomposeJoin_face_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      s.postcomposeJoin q = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (s.postcompose q).square).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, Category.assoc,
      postcomposeJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeLower q).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [postcomposeLower_face_two]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (s.postcompose q).square)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, Category.assoc,
      postcomposeJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((s.postcomposeUpper q).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [postcomposeUpper_face_two]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (s.postcompose q).square)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin (postcomposeJoin_face_zero)


end SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquarePostcomposeJoin

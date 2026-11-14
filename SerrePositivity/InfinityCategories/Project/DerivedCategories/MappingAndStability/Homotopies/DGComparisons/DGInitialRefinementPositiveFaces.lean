module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementFixedSourceFaces

/-! # 正番号の coface と任意次数の閉始点細分

概要：正番号の coface は零を固定し、その制限は同じ閉始点細分と厳密に可換。
方針：単射面に対する一般の可換性を coface へ適用する。
規約：始対象の型の輸送を明示する。使われ方：四次最後ホーンの六つの重なり。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded

/-- 正番号の coface は、最初の頂点零を厳密に保つ。 -/
lemma dgPositiveCoface_zero {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0) :
    (SimplexCategory.δ j).toOrderHom 0 = 0 := by
  obtain ⟨i, rfl⟩ := j.eq_succ_of_ne_zero hj
  change i.succ.succAbove 0 = 0
  simp

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 任意次数の実単体の正番号の面は、元の面を同じ閉射で細分したもの。 -/
lemma dgSimplexInitialRefinement_face_positive {n : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1))
    (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))
    (j : Fin (n + 2)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s).pullback (SimplexCategory.δ j).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D (t.pullback (SimplexCategory.δ j).toOrderHom) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (congrArg t.obj (dgPositiveCoface_zero j hj).symm)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_pullback_fixed_zero A D t q s _ j.succAboveOrderEmb.injective
    (dgPositiveCoface_zero j hj)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverBoundaryRefinedSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverInitialRefinementReindex

/-! # 一般回収 over 単体の正番号面を同じ元の境界面の細分へ同定する

概要：元のホーンの正番号面を実 over 境界面の回収単体へ戻し、同じ閉細分を比較する。
方針：米田表示の面公式と、追加閉射の実辺の保存を使う。
規約：全対象の等式輸送を明示。使われ方：新 apex の実分母性と共有面の厳密一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (B : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)

/-- 実境界の各回収単体は、元のホーンの同じ番号の指定面。 -/
lemma dgOverBoundaryCanonicalFace (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornCanonicalFace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn a B) j.castSucc
      (Fin.castSucc_ne_last j) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a (SSet.yonedaEquiv (boundary.ι j ≫ B))) := by
  refine (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornCanonicalFace_eq _ _ _).trans ?_
  have he := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn_face a B j)
  rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] at he
  exact he

/-- 正番号面の回収単体の始対象は、元の同じホーン始対象。 -/
lemma dgOverBoundaryFace_source (j : Fin (n + 2)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn a B)).obj 0 =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a (SSet.yonedaEquiv (boundary.ι j ≫ B)))).obj 0 :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn a B)).obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPositiveCoface_zero j.castSucc (Fin.castSucc_ne_zero_iff.mpr hj)).symm).trans
      (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1) => t.obj 0) (dgOverBoundaryCanonicalFace a B j))

/-- 全正番号面は、元の実 over 境界面の同じ閉始点細分である。 -/
lemma dgOverBoundaryRefinedSimplex_face_initial (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn a B)).obj 0))
    (F : Δ[n + 2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn a B) q s)
    (j : Fin (n + 2)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ j (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverBoundaryRefinedSimplex a B q s F hF) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a (SSet.yonedaEquiv (boundary.ι j ≫ B)) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgOverBoundaryFace_source a B j hj)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_injective a
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverBoundaryRefinedSimplex_face_positive a B q s F hF j hj,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialMap
  apply congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr (dgOverBoundaryCanonicalFace a B j) q q
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories

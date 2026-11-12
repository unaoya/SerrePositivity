module
public import SerrePositivity.KST.SConstruction.StrictZeroSOne
public import SerrePositivity.KST.SConstruction.SingleObjLoopNaturality

/-! # 逆向き K₀ 写像による対象類の回収
概要：元の BF K 群から三角圏 K₀ への写像は対象類を保つ。
方針：同じ零対角を持つ閉じた S₁ 辺を選び、実ホモトピーの自然性を使う。
規約：元の全零境界商と既存の Kan 置換を保持する。
使われ方：π₀ K と三角圏 K₀ の比較の逆律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 閉じた元の S₁ 辺の Kan 境界上の評価は負の対象類。 -/
lemma boundaryKanTriangulatedMap_closed_edge (X : StableModel.{u})
    (d : (objectSConstruction X.carrier) _⦋1⦌)
    (hd : (objectSConstruction X.carrier).δ 0 d = (objectSConstruction X.carrier).δ 1 d) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (boundaryKanTriangulatedMap X)).map
      (SSet.Truncated.HomotopyCategory.homMk
        (fundamentalLoopEdge (objectBoundaryEdge X d)))).down.toAdd =
      -objectTriangulatedClass X d := by
  let e : SSet.Truncated.Edge (X := (truncation 2).obj (objectSConstruction X.carrier))
      ((objectSConstruction X.carrier).δ 1 d) ((objectSConstruction X.carrier).δ 1 d) :=
    ⟨d, rfl, hd⟩
  let α := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fundamentalNerveUntransposeHomotopy (rawBoundaryTriangulatedHomotopy X)
  have h := singleObj_loop_naturality α.hom (SSet.Truncated.HomotopyCategory.homMk e)
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose
      (objectRawBoundaryComparison X ≫ rawBoundaryTriangulatedMap X) =
      (hoFunctor.map (objectBoundaryKanComparison X)).toFunctor ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (boundaryKanTriangulatedMap X) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose_pre, ← objectRawBoundaryComparison_kan,
      Category.assoc, boundaryKanTriangulatedMap_unit]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose
      (objectRawBoundaryComparison X ≫ rawBoundaryTriangulatedMap X) |>.map
        (SSet.Truncated.HomotopyCategory.homMk e)).down.toAdd =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (objectTriangulatedNerveMap X) |>.map
        (SSet.Truncated.HomotopyCategory.homMk e)).down.toAdd at h
  rw [hf, objectTriangulatedNerveMap_untranspose] at h
  simp only [CategoryTheory.Functor.comp_map] at h
  have hm : (hoFunctor.map (objectBoundaryKanComparison X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map (objectBoundaryKanComparison X))) := rfl
  rw [hm] at h
  change _ = ((objectTriangulatedFunctor X).map
    (SSet.Truncated.HomotopyCategory.homMk e)).toAdd at h
  rw [objectTriangulatedFunctor_map_edge] at h
  have he : (e.map ((truncation 2).map (objectBoundaryKanComparison X))).edge =
      (fundamentalLoopEdge (objectBoundaryEdge X d)).edge := by
    change (objectBoundaryKanComparison X).app _ d =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm d ≫ objectBoundaryKanComparison X)
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (singleObj_edge_value_congr _ _ _ he).symm.trans h

/-- 逆向き準同型は元の任意の対象の K 類から同じ三角圏 K₀ 類を回収する。 -/
lemma kZeroToTriangulatedMap_object (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    kZeroToTriangulatedMap X (objectKClass X x) =
      TriangulatedK0.mk (C := hoFunctor.obj X.carrier) (SSet.HomotopyCategory.mk x) := by
  obtain ⟨e, he, hc⟩ := exists_closedObjectSOne x
  rw [← he, kZeroToTriangulatedMap_object_formula, boundaryKanTriangulatedMap_closed_edge X e hc,
    neg_neg]
  rfl

end SerrePositivity.KST.SConstruction

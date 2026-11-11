module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoconeLegComposition

/-!
概要：元の余錐の脚は、底の指定辺に沿う元の transition とホモトピーまで可換。
方針：指定辺と余錐頂点の join を同じ二単体として読み戻す。
規約：底の辺・図式・余錐を変更しない。
使われ方：filtered な後続段階での同一視を全空間へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 底の同じ辺と余錐頂点は、元の両脚との合成を表す二単体を与える。 -/
def coconeLegNaturalityTriangle {B X : SSet.{u}} {F : B ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
    {x y : B _⦋0⦌} (e : B.Edge x y) :
    (e.map F).CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c x) := by
  let a := SSet.yonedaEquiv.symm e.edge
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a (𝟙 Δ[0]) ≫ c.val
  have he (i : Fin 2) : stdSimplex.δ i ≫ a =
      SSet.yonedaEquiv.symm (B.δ i e.edge) := by
    apply SSet.yonedaEquiv.injective
    simp only [stdSimplex.yonedaEquiv_δ_comp, a, Equiv.apply_symm_apply]
  have hv (i : Fin 2) : stdSimplex.δ i.castSucc ≫ T =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i ≫ a) (𝟙 Δ[0]) ≫ c.val := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex, Category.assoc]
    dsimp [T]
    rw [Iso.hom_inv_id_assoc]
    simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  refine SSet.Edge.CompStruct.ofTruncated
    { simplex := SSet.yonedaEquiv T, d₂ := ?_, d₀ := ?_, d₁ := ?_ }
  · change X.δ 2 (SSet.yonedaEquiv T) = (e.map F).edge
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have ht : stdSimplex.δ (2 : Fin 3) ≫ T = a ≫ F := by
      dsimp [T]
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inl, Category.assoc, Iso.hom_inv_id_assoc,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, c.property]
    rw [ht, SSet.yonedaEquiv_comp]
    exact congrArg (F.app (Opposite.op ⦋1⦌)) (SSet.yonedaEquiv.apply_symm_apply e.edge)
  · change X.δ 0 (SSet.yonedaEquiv T) = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c y).edge
    have h := hv (0 : Fin 2)
    change stdSimplex.δ (0 : Fin 3) ≫ T = _ at h
    rw [← stdSimplex.yonedaEquiv_δ_comp, h, he, e.tgt_eq]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg_edge c y).symm
  · change X.δ 1 (SSet.yonedaEquiv T) = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c x).edge
    have h := hv (1 : Fin 2)
    change stdSimplex.δ (1 : Fin 3) ≫ T = _ at h
    rw [← stdSimplex.yonedaEquiv_δ_comp, h, he, e.src_eq]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg_edge c x).symm

/-- 指定された底の辺に沿い、同じ元の脚と transition の合成がホモトピック。 -/
def coconeLegNaturalityHomotopy {B : SSet.{u + 1}} {F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {x y : B _⦋0⦌} (e : B.Edge x y) :
    Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c x))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (e.map F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c y)) := by
  let t := coconeLegNaturalityTriangle c e
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityTriangleHomotopy_of_faces _ _ _ t.simplex
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue_edge]
    exact t.d₂
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue_edge]
    exact t.d₀
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue_edge]
    exact t.d₁

set_option maxHeartbeats 1000000 in
-- 元の脚と transition の投影された Kan 型の展開が標準 heartbeat を超えるため、局所的に増やす。
/-- 底の元の辺に沿って押し出しても、同じ脚の像の連結成分は変わらない。 -/
lemma coconeLegNaturality_components {B : SSet.{u + 1}} {F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {x y : B _⦋0⦌} (e : B.Edge x y)
    (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) x)).obj _⦋0⦌) :
    π₀.mk ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c y)).app _
        ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (e.map F)).app _ a)) =
      π₀.mk ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c x)).app _ a) :=
  (π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coconeLegNaturalityHomotopy c e) a)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

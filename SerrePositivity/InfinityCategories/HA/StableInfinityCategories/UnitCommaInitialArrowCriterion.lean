module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UnitCommaArrowNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-!
概要：固定始域 comma の実矢印と始対象性、指定 loop 単位の可逆性。
方針：実ホモトピーの Ho 自然性と left fibration の可逆性反映を使う。
規約：生の関手値の端点を保つ。使われ方：元の loop 四角形の押し出し性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma unitCommaFiber_isInitial_of_invertibleArrow {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G)
    (x : X _⦋0⦌) (u : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex u)
    (huA : IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x u))
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (hvA : IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  obtain ⟨e⟩ := hu.nonempty_edge v
  let m := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)) ≫ G)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk e)
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom_naturality_edge G x e
  have := huA
  have := hvA
  have : IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x u ≫ m) := h ▸ hvA
  have hm : IsIso m := by
    have hf : inv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x u) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x u ≫ m) = m := by simp
    exact hf ▸ (inferInstance : IsIso (inv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x u) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x u ≫ m)))
  let π := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x
  have hmap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      ((e.map ((truncation 2).map π)).map ((truncation 2).map G)) := by
    change IsIso m
    exact hm
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge π e
    (hG.reflects_isInvertibleEdge (e.map ((truncation 2).map π)) hmap)
  exact hu.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk e))

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma unitCommaFiber_isInitial_iff_invertibleArrow {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G)
    (x : X _⦋0⦌) (u : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex u)
    (huA : IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x u))
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v ↔ IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x v) := by
  constructor
  · intro hv
    obtain ⟨e⟩ := hu.nonempty_edge v
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e :=
      CategoryTheory.Limits.isIso_of_isInitial hu.isInitialHo hv.isInitialHo _
    have := huA
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom_naturality_edge G x e]
    infer_instance
  · exact unitCommaFiber_isInitial_of_invertibleArrow G hG x u hu huA v
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

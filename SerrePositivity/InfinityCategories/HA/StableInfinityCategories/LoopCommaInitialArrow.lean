module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UnitCommaInitialArrowCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSourceUnitInvertible
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UnitCommaSectionArrow

/-!
概要：指定 loop 単位と任意の実パラメータ族の comma 矢印の可逆性。
方針：端点輸送を Arrow の等号に保ち、同じ一次単体を照合する。
規約：追加の基準矢印の可逆性を仮定しない。使われ方：元の loop 四角形の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma loopUnitCommaFiber_isInitial_iff_invertibleArrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v ↔ IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x v) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSourceUnit_isIso s hs hΩ
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiber_isInitial_iff_invertibleArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ).isFullyFaithful
    x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSourceUnit s hs hΩ) x)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSourceUnit_initial s hs hΩ x)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom_section_isIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSourceUnit s hs hΩ) x) v
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

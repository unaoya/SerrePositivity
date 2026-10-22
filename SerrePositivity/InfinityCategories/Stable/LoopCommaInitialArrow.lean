module
public import SerrePositivity.InfinityCategories.Stable.UnitCommaInitialArrowCriterion
public import SerrePositivity.InfinityCategories.Stable.LoopSourceUnitInvertible
public import SerrePositivity.InfinityCategories.Stable.UnitCommaSectionArrow

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
namespace SerrePositivity.InfinityCategories

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma loopUnitCommaFiber_isInitial_iff_invertibleArrow {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌)
    (v : (unitCommaFiber (loopDiagramEvaluation X 0 0) x) _⦋0⦌) :
    IsInitialVertex v ↔ IsIso (unitCommaFiberArrowHom (loopDiagramEvaluation X 0 0) x v) := by
  have := loopSourceUnit_isIso s hs hΩ
  exact unitCommaFiber_isInitial_iff_invertibleArrow (loopDiagramEvaluation X 0 0)
    (loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ).isFullyFaithful
    x (unitCommaSectionVertex (loopSourceUnit s hs hΩ) x)
    (loopSourceUnit_initial s hs hΩ x)
    (unitCommaFiberArrowHom_section_isIso (loopSourceUnit s hs hΩ) x) v
end SerrePositivity.InfinityCategories

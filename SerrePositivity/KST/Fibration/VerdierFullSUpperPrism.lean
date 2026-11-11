module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanPrismIso
public import SerrePositivity.KST.Fibration.ZeroMiddleVerdierCoordinates

/-!
概要：同じ全 S• 中間対象への三角柱同型を、指定 Verdier 四角形の元の上側二胞体へ接続する。
方針：元の上側二単体の読出しと native 正反復座標を厳密照合する。
規約：終端は元の四角形の全上側二胞体。共有対角と元の三角柱の辺を保持する。
使われ方：K-6 c4 の指定上下二胞体を保つ全四角形比較への上側入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 元の上側二単体の native 像は、元の指定四角形の同じ上側三角形の全射。 -/
theorem verdierFullSUpperPrism_original :
    SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) (verdierUpperTriangle d)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) := by
  rw [stableCoreSingleKanInfinity_eq]
  have h := SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (0 : Fin 2)))
    (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
  simpa only [Equiv.symm_apply_apply, verdierUpperTriangle, NatTrans.comp_app_apply] using! h.symm

/-- 元の指定四角形の同じ全上側二胞体へ終わる、全 S• 中間対象の実三角柱。 -/
def verdierFullSUpperPrism : SSet.Homotopy
    (zeroMiddleFullSKanTransportedTriangle (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) where
  h := (zeroMiddleFullSKanPrism (verdierUpperTriangle d) (verdierUpperTriangle_middle_isZero d)).h
  h₀ := (zeroMiddleFullSKanPrism (verdierUpperTriangle d) (verdierUpperTriangle_middle_isZero d)).h₀
  h₁ := (zeroMiddleFullSKanPrism (verdierUpperTriangle d)
    (verdierUpperTriangle_middle_isZero d)).h₁.trans (verdierFullSUpperPrism_original d)
  rel := by ext n t; exact False.elim t.1.2

/-- 元の指定上側二胞体へ戻る同じ三角柱は、全頂点で元の可逆な縦辺を保つ。 -/
theorem verdierFullSUpperPrism_pointwise :
    ∀ k : (Δ[2] : SSet.{u + 1}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierFullSUpperPrism d) k).toTruncated := by
  intro k
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierFullSUpperPrism d) k).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleFullSKanPrism (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d)) k).toTruncated) rfl).mpr
  exact zeroMiddleFullSKanPrism_pointwise (verdierUpperTriangle d)
    (verdierUpperTriangle_middle_isZero d) k

/-- 元の全上側二胞体を終端とする同じ実三角柱の全関手同型。 -/
def verdierFullSUpperPrismIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (zeroMiddleFullSKanTransportedTriangle (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _ (verdierFullSUpperPrism_pointwise d)

/-- 指定全上側二胞体への同じ実三角柱は、共有対角を全時刻固定する。 -/
theorem verdierFullSUpperPrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierFullSUpperPrism d).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        stdSimplex.δ (1 : Fin 3) ≫ zeroMiddleFullSKanTransportedTriangle (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) :=
  zeroMiddleFullSKanPrism_diagonal _ _

end SerrePositivity.KST.Fibration

module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerSquareFixedSpanInclusion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareFixedSpanPoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerSquareSourcePointInitial

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma zeroCornerSquare_isPushout_of_sourcePoint_initial {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] {x : X _⦋0⦌}
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) x) _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) (F : Δ[1] ⊗ Δ[1] ⟶ X)
    (hF : z.val.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  let b := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) z.val
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X) b) _⦋0⦌ :=
    ⟨z.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSourcePoint_fixedSpan_isInitial z hz
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareFixedSpanRawIso X b
  have hw := hv.map_of_isIso e.hom
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareFixedSpan_isPushout_of_initial _ hw F
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareFixedSpanRawIso_hom_ι X b)
      (Opposite.op ⦋0⦌)) v
  exact he.trans hF

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

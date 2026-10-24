module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareFixedSpanInitial

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
namespace SerrePositivity.InfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma zeroCornerSquareSourcePoint_fixedSpan_isInitial {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] {x : X _⦋0⦌}
    (z : (vertexFiber (zeroCornerSquareSource X) x) _⦋0⦌)
    (hz : IsInitialVertex z) :
    IsInitialVertex (X := vertexFiber (zeroCornerSquareSpan X)
      ((zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) z.val))
      ⟨z.val, (pinchedConstant_zero _).symm⟩ := by
  let p := zeroCornerSquareSpanSourceFiberMap X x
  let b := p.app (Opposite.op ⦋0⦌) z
  let v : (vertexFiber p b) _⦋0⦌ := ⟨z, (pinchedConstant_zero _).symm⟩
  have hp : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting p :=
    zeroCornerSquareSpanSourceFiberMap_kanEquivalenceLifting X x
  have := hp.innerFibration
  have : Quasicategory (vertexFiber p b) := innerFibration_vertexFiber_quasicategory p b
  let e := (vertexFiberι_isQCatEquivalence_of_contractible_base_of_equivalenceLifting
    p hp (zeroOuterSpanSourceFiber_isContractibleKan X x) b).choose
  have hv : IsInitialVertex v := (e.isInitialVertex_iff v).mpr hz
  let g := HomotopyLimits.vertexFiberMapFiberIso
    (zeroCornerSquareSource X) (zeroOuterSpanSource X) (zeroCornerSquareSpan X)
    (zeroCornerSquareSpan_source X) x b
  exact hv.map_of_isIso g.hom

end SerrePositivity.InfinityCategories

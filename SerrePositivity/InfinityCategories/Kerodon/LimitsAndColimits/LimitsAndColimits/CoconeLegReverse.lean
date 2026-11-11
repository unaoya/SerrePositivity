module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeEquiv

/-!
概要：反転と図式同型による余錐の脚の比較を整備する。
方針：join の混合辺と固定図式の輸送の射を計算する。
規約：添字や標的の quasicategory 性を追加で要求しない。
使われ方：B5 の指定単位を伴う左 Kan の局所余錐の比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 概要：余錐の指定対象から頂点へ入る混合一次単体を表示する。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
def joinCoconeLegSimplex {K : SSet.{u}} (x : K _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl x (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))

/-- 概要：錐の頂点から指定対象へ出る混合一次単体を表示する。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
def joinConeLegSimplex {K : SSet.{u}} (x : K _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) x

/-- 概要：join の反転は余錐の混合辺を錐の混合辺へ移す。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
lemma joinReverse_coconeLeg {K : SSet.{u}} (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K (Δ[0] : SSet.{u})).hom.app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (joinCoconeLegSimplex x)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op)).app (Opposite.op ⦋1⦌)
          (joinConeLegSimplex (SSet.opObjEquiv.symm x)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePairEquiv K (Δ[0] : SSet.{u}) 2) (joinCoconeLegSimplex x) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op)).app (Opposite.op ⦋1⦌)
      (joinConeLegSimplex (SSet.opObjEquiv.symm x))
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoin_hext _ _ rfl ?_ ?_
  · apply heq_of_eq
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv (Δ[0] : SSet.{u}) 1).injective
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePair_left K (Δ[0] : SSet.{u}) 2
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K Δ[0] 2 from joinCoconeLegSimplex x)]
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  · apply heq_of_eq
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv K 1).injective
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePair_right K (Δ[0] : SSet.{u}) 2
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K Δ[0] 2 from joinCoconeLegSimplex x)]

/-- 概要：余錐を反転した錐の脚は元の余錐の脚の反転。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
lemma coconeReverseCone_leg {K X : SSet.{u}} {p : K ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone d).val.app (Opposite.op ⦋1⦌)
      (joinConeLegSimplex (SSet.opObjEquiv.symm x)) =
        SSet.opObjEquiv.symm (d.val.app (Opposite.op ⦋1⦌) (joinCoconeLegSimplex x)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_val]
  change (SSet.opFunctor.map d.val).app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[0]).inv.app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op)).app (Opposite.op ⦋1⦌)
        (joinConeLegSimplex (SSet.opObjEquiv.symm x)))) = _
  rw [← joinReverse_coconeLeg]
  change (SSet.opFunctor.map d.val).app (Opposite.op ⦋1⦌)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[0]).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[0]).inv).app
      (Opposite.op ⦋1⦌) (SSet.opObjEquiv.symm (joinCoconeLegSimplex x))) = _
  rw [Iso.hom_inv_id]
  rfl

/-- 概要：join の混合辺は右因子の射の作用と可換。
方針：混合辺の頂点と切断の定義を計算する。
規約：任意の単体集合の射を扱う。
使われ方：反転した余錐の脚の添字変更。 -/
lemma joinConeLegSimplex_natural {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) f).app (Opposite.op ⦋1⦌) (joinConeLegSimplex x) =
      joinConeLegSimplex (f.app (Opposite.op ⦋0⦌) x) := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

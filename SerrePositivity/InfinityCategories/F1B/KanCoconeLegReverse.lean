module

public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconeEquiv

/-!
概要：反転と図式同型による余錐の脚の比較を整備する。
方針：join の混合辺と固定図式の輸送の射を計算する。
規約：添字や標的の quasicategory 性を追加で要求しない。
使われ方：B5 の指定単位を伴う左 Kan の局所余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B


/-- 概要：余錐の指定対象から頂点へ入る混合一次単体を表示する。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
def kanJoinCoconeLegSimplex {K : SSet.{u}} (x : K _⦋0⦌) : (join K (Δ[0] : SSet.{u})) _⦋1⦌ :=
  Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl x (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))

/-- 概要：錐の頂点から指定対象へ出る混合一次単体を表示する。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
def kanJoinConeLegSimplex {K : SSet.{u}} (x : K _⦋0⦌) : (join (Δ[0] : SSet.{u}) K) _⦋1⦌ :=
  Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) x

/-- 概要：join の反転は余錐の混合辺を錐の混合辺へ移す。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
lemma kanJoinReverse_coconeLeg {K : SSet.{u}} (x : K _⦋0⦌) :
    (stableJoinReverseIso K (Δ[0] : SSet.{u})).hom.app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (kanJoinCoconeLegSimplex x)) =
        (joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op)).app (Opposite.op ⦋1⦌)
          (kanJoinConeLegSimplex (SSet.opObjEquiv.symm x)) := by
  change (stableAugJoinReversePairEquiv K (Δ[0] : SSet.{u}) 2) (kanJoinCoconeLegSimplex x) =
    (joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op)).app (Opposite.op ⦋1⦌)
      (kanJoinConeLegSimplex (SSet.opObjEquiv.symm x))
  refine stableAugJoin_hext _ _ rfl ?_ ?_
  · apply heq_of_eq
    apply (stableAugOpEquiv (Δ[0] : SSet.{u}) 1).injective
    erw [stableAugJoinReversePair_left K (Δ[0] : SSet.{u}) 2
      (show StableAugJoin K Δ[0] 2 from kanJoinCoconeLegSimplex x)]
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  · apply heq_of_eq
    apply (stableAugOpEquiv K 1).injective
    erw [stableAugJoinReversePair_right K (Δ[0] : SSet.{u}) 2
      (show StableAugJoin K Δ[0] 2 from kanJoinCoconeLegSimplex x)]

/-- 概要：余錐を反転した錐の脚は元の余錐の脚の反転。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
lemma kanCoconeReverseCone_leg {K X : SSet.{u}} {p : K ⟶ X} (d : JoinCocone p) (x : K _⦋0⦌) :
    (kanCoconeReverseCone d).val.app (Opposite.op ⦋1⦌)
      (kanJoinConeLegSimplex (SSet.opObjEquiv.symm x)) =
        SSet.opObjEquiv.symm (d.val.app (Opposite.op ⦋1⦌) (kanJoinCoconeLegSimplex x)) := by
  rw [kanCoconeReverseCone_val]
  change (SSet.opFunctor.map d.val).app (Opposite.op ⦋1⦌)
    ((stableJoinReverseIso K Δ[0]).inv.app (Opposite.op ⦋1⦌)
      ((joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op)).app (Opposite.op ⦋1⦌)
        (kanJoinConeLegSimplex (SSet.opObjEquiv.symm x)))) = _
  rw [← kanJoinReverse_coconeLeg]
  change (SSet.opFunctor.map d.val).app (Opposite.op ⦋1⦌)
    (((stableJoinReverseIso K Δ[0]).hom ≫ (stableJoinReverseIso K Δ[0]).inv).app
      (Opposite.op ⦋1⦌) (SSet.opObjEquiv.symm (kanJoinCoconeLegSimplex x))) = _
  rw [Iso.hom_inv_id]
  rfl

/-- 概要：join の混合辺は右因子の射の作用と可換。
方針：混合辺の頂点と切断の定義を計算する。
規約：任意の単体集合の射を扱う。
使われ方：反転した余錐の脚の添字変更。 -/
lemma kanJoinConeLegSimplex_natural {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    (joinMap (𝟙 (Δ[0] : SSet.{u})) f).app (Opposite.op ⦋1⦌) (kanJoinConeLegSimplex x) =
      kanJoinConeLegSimplex (f.app (Opposite.op ⦋0⦌) x) := rfl

end SerrePositivity.InfinityCategories.F1B

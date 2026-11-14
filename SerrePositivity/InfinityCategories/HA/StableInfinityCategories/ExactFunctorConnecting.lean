module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorCofiberComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorSuspensionObjectComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnectingNaturality

/-! # 完全関手と懸垂に値を持つ接続射

概要：完全関手は懸垂比較を介して cofiber 接続射を保つ。
方針：指定 suspension への接続射の保存と対象比較の逆射との両立を合成する。
規約：選択済みの接続射と懸垂関手を使う。使われ方：h の三角関手の第三射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：完全関手で写した接続射に懸垂比較を合成すると、像の列の接続射になる。
方針：任意の指定 suspension を介して両辺を表示し、接続射と対象比較をそれぞれ写す。
規約：安定な quasicategory 間の完全関手。使われ方：cofiber 三角形の保存。 -/
lemma cofiberConnecting_postcomp {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) :
    (hoFunctor.map F).toFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)
  let H := (hoFunctor.map F).toFunctor
  calc
    H.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁ =
        (H.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s) ≫
          H.map s.suspensionFunctorObjIso.inv) ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁ := by
      rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_objIso_inv t ht s]
      exact congrArg (fun a ↦ a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁)
        (H.map_comp _ _)
    _ = H.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s) ≫ (s.map F).suspensionFunctorObjIso.inv := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun a ↦ H.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s) ≫ a)
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctor_map_objIso_inv_comp_suspensionIso F s))
    _ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) (s.map F) ≫
          (s.map F).suspensionFunctorObjIso.inv := by
      exact congrArg (fun a ↦ a ≫ (s.map F).suspensionFunctorObjIso.inv)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_postcomp F t ht s)
    _ = _ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_objIso_inv _ _ _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

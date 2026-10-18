module
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorCofiberComparison
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorSuspensionObjectComparison
public import SerrePositivity.InfinityCategories.Stable.CofiberConnectingNaturality

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
namespace SerrePositivity.InfinityCategories

/-- 概要：完全関手で写した接続射に懸垂比較を合成すると、像の列の接続射になる。
方針：任意の指定 suspension を介して両辺を表示し、接続射と対象比較をそれぞれ写す。
規約：安定な quasicategory 間の完全関手。使われ方：cofiber 三角形の保存。 -/
lemma cofiberConnecting_postcomp {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] (t : ZeroTriangle X) (ht : IsCofiberSequence t) :
    (hoFunctor.map F).toFunctor.map (cofiberConnecting t ht) ≫
        (exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁ =
      cofiberConnecting (t.map F (IsExactFunctor.preservesZero (F := F)))
        (IsExactFunctor.preservesCofiber (F := F) t ht) := by
  let s := chosenSuspensionSquare (squareVertex t.square 0 0)
  let H := (hoFunctor.map F).toFunctor
  calc
    H.map (cofiberConnecting t ht) ≫ (exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁ =
        (H.map (cofiberConnectingToSuspension t ht s) ≫
          H.map s.suspensionFunctorObjIso.inv) ≫
          (exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁ := by
      rw [← cofiberConnectingToSuspension_comp_objIso_inv t ht s]
      exact congrArg (fun a ↦ a ≫ (exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁)
        (H.map_comp _ _)
    _ = H.map (cofiberConnectingToSuspension t ht s) ≫ (s.map F).suspensionFunctorObjIso.inv := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun a ↦ H.map (cofiberConnectingToSuspension t ht s) ≫ a)
          (exactFunctor_map_objIso_inv_comp_suspensionIso F s))
    _ = cofiberConnectingToSuspension (t.map F (IsExactFunctor.preservesZero (F := F)))
        (IsExactFunctor.preservesCofiber (F := F) t ht) (s.map F) ≫
          (s.map F).suspensionFunctorObjIso.inv := by
      exact congrArg (fun a ↦ a ≫ (s.map F).suspensionFunctorObjIso.inv)
        (cofiberConnectingToSuspension_postcomp F t ht s)
    _ = _ := cofiberConnectingToSuspension_comp_objIso_inv _ _ _

end SerrePositivity.InfinityCategories

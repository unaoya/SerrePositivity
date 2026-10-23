module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackPushout
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorCorePushout
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackHomFunctor

/-!
概要：底の pushout に沿って、元の標的へ写す cocartesian Hom の core を貼る。
方針：全空間の pushout と同じ指定辺の被覆を、指定辺保存 Hom の core に適用する。
規約：可変の底は任意の単体集合でよい。
使われ方：元の分類 Hom の高次セルへの還元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ局所 cocartesian Hom の core は、底の pushout を厳密な pullback へ写す。 -/
lemma core_cocartesianPullbackHomPre_isPullback_of_isPushout
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    {a b c d : Over B} (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
    [Mono g.left] (hp : IsPushout f.left g.left i.left j.left) :
    IsPullback (quasicategoryCoreMap (cocartesianPullbackHomPre p q j))
      (quasicategoryCoreMap (cocartesianPullbackHomPre p q i))
      (quasicategoryCoreMap (cocartesianPullbackHomPre p q g))
      (quasicategoryCoreMap (cocartesianPullbackHomPre p q f)) := by
  letI : Mono g := Over.mono_of_mono_left g
  let K := Over.pullback p ⋙ Over.map p
  have hK : IsPushout (K.map f).left (K.map g).left (K.map i).left (K.map j).left :=
    overPullbackUnderlying_isPushout p f g i j hp
  letI : Mono (K.map g).left := inferInstanceAs (Mono ((overPullbackUnderlying p).map g))
  exact core_markedCocartesianFunctorPre_isPullback_of_isPushout q
    (K.map f) (K.map g) (K.map i) (K.map j) hK
    {e | IsCocartesianEdge (pullback.fst a.hom p) e}
    {e | IsCocartesianEdge (pullback.fst b.hom p) e}
    {e | IsCocartesianEdge (pullback.fst c.hom p) e}
    {e | IsCocartesianEdge (pullback.fst d.hom p) e}
    (fun e he ↦ isCocartesianEdge_overPullback_map p f e he)
    (fun e he ↦ isCocartesianEdge_overPullback_map p g e he)
    (fun e he ↦ isCocartesianEdge_overPullback_map p i e he)
    (fun e he ↦ isCocartesianEdge_overPullback_map p j e he)
    (cocartesianPullback_pushout_markCover p f g i j hp)

end SerrePositivity.InfinityCategories

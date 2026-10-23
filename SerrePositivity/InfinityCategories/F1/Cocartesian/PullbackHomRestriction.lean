module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackDomainMarks
public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorPrecomposition

/-!
概要：底の各対象への引き戻しに、元の cocartesian Hom を制限する。
方針：各底変換に固有の指定辺を保つ相対 Hom を使い、元の全空間への射で前合成する。
規約：標的の全空間は元のまま保持し、底を変えた標的との同型は別に比較する。
使われ方：元の分類写像の Hom を底のセルに沿って検証するための制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の標的へ写す各底変換の相対 Hom。指定辺は各底変換に固有の cocartesian 辺。 -/
def cocartesianPullbackHomSpace {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (a : Over B) :
    SSet.{u} :=
  markedCocartesianFunctorSpace q (pullback.snd a.hom p ≫ p)
    {e | IsCocartesianEdge (pullback.fst a.hom p) e}

/-- 底上の射による、元の各底変換の相対 Hom の制限。 -/
def cocartesianPullbackHomPre {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) {a b : Over B} (f : a ⟶ b) :
    cocartesianPullbackHomSpace p q b ⟶ cocartesianPullbackHomSpace p q a :=
  markedCocartesianFunctorPre q ((Over.pullback p ⋙ Over.map p).map f)
    {e | IsCocartesianEdge (pullback.fst a.hom p) e}
    {e | IsCocartesianEdge (pullback.fst b.hom p) e}
    (fun e he ↦ isCocartesianEdge_overPullback_map p f e he)

/-- 元の全 cocartesian Hom を各底変換へ、同じ全相対作用で制限する。 -/
def cocartesianPullbackHomRestriction {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) (a : Over B) :
    cocartesianRelativeFunctorSpace p q ⟶ cocartesianPullbackHomSpace p q a :=
  markedCocartesianFunctorPre q
    (Over.homMk (U := Over.mk (pullback.snd a.hom p ≫ p)) (V := Over.mk p)
      (pullback.snd a.hom p) rfl)
    {e | IsCocartesianEdge (pullback.fst a.hom p) e} {e | IsCocartesianEdge p e}
    (fun e he ↦ (isCocartesianEdge_overPullback_iff p a e).mp he)

end SerrePositivity.InfinityCategories

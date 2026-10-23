module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsPullbackNaturality
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianStrictTransport

/-!
概要：通常圏の関手による strict transport の底変換比較の元の成分を構成する。
方針：under の関手で元の section を制限し、同じ pullback の全空間へ持ち上げる。
規約：元の fibration の両射影を底変換した側を標的とする。
使われ方：分類主写像のセル制限と実際の底変換の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 底の関手が誘導する under の関手を、元の底の nerve 上の射とする。 -/
def cocartesianStrictTransportUnderPost {C D : Type u} [Category.{u} C] [Category.{u} D]
    (k : D ⥤ C) (d : D) :
    Over.mk (nerveMap (Under.forget d) ≫ nerveMap k) ⟶
      Over.mk (nerveMap (Under.forget (k.obj d))) :=
  Over.homMk (nerveMap (Under.post k)) rfl

/-- 元の strict transport の値を、各底変換の元の strict transport の値へ写す。 -/
def cocartesianStrictTransportBaseChangeComponent
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (k : D ⥤ C) (d : D) :
    kanCocartesianStrictTransport p (k.obj d) ⟶
      kanCocartesianStrictTransport (pullback.fst (nerveMap k) p) d :=
  kanCocartesianSectionsPre p (cocartesianStrictTransportUnderPost k d) ≫
    (cocartesianSectionsPullbackIso (IsPullback.of_hasPullback (nerveMap k) p).flip
      (nerveMap (Under.forget d)) (nerveMap (Under.forget d) ≫ nerveMap k) rfl).inv

/-- 同じ成分を元の標的へ戻すと、元の under の関手による section の制限になる。 -/
lemma cocartesianStrictTransportBaseChangeComponent_iso
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (k : D ⥤ C) (d : D) :
    cocartesianStrictTransportBaseChangeComponent p k d ≫
      (cocartesianSectionsPullbackIso (IsPullback.of_hasPullback (nerveMap k) p).flip
        (nerveMap (Under.forget d)) (nerveMap (Under.forget d) ≫ nerveMap k) rfl).hom =
      kanCocartesianSectionsPre p (cocartesianStrictTransportUnderPost k d) := by
  simp only [cocartesianStrictTransportBaseChangeComponent, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 同じ比較成分の全パラメーターの展開は、under の実際の始域の制限である。 -/
lemma cocartesianStrictTransportBaseChangeComponent_uncurry_snd
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E T : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (k : D ⥤ C) (d : D)
    (s : T ⟶ kanCocartesianStrictTransport p (k.obj d)) :
    relativeFunctorUncurry ((s ≫ cocartesianStrictTransportBaseChangeComponent p k d) ≫
      kanCocartesianSectionsι (pullback.fst (nerveMap k) p) (nerveMap (Under.forget d))) ≫
      pullback.snd (nerveMap k) p =
    (nerveMap (Under.post k) ▷ T) ≫ relativeFunctorUncurry
      (s ≫ kanCocartesianSectionsι p (nerveMap (Under.forget (k.obj d)))) := by
  unfold cocartesianStrictTransportBaseChangeComponent
  rw [← Category.assoc s]
  refine (cocartesianSectionsPullbackIso_inv_uncurry
    (IsPullback.of_hasPullback (nerveMap k) p).flip (nerveMap (Under.forget d))
    (nerveMap (Under.forget d) ≫ nerveMap k) rfl
    (s ≫ kanCocartesianSectionsPre p (cocartesianStrictTransportUnderPost k d))).trans ?_
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  rfl

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ReverseTransportComparison

/-!
概要：元の反転合成 prism の底の全族と、その二端を同じ実表示で公開する。
方針：元の第一 Hom の反転区間へ第二射影を前合成する。
規約：二つの全 Hom を保持。使われ方：元の指定対角比較の後合成自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C)

/-- 元の反転合成 prism が被覆する、同じ二 Hom 全体上の実区間。 -/
def coherentReverseCompositionBase :=
  (Δ[1] ◁ snd
    (((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)).op)
    (((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op)) ≫
      coherentReverseHomInterval X Y

/-- 元の底の全区間の始点は、同じ元の中間対象。 -/
lemma coherentReverseCompositionBase_zero :
    prismEndpoint 0 _ ≫ coherentReverseCompositionBase X Y Z =
      SSet.const (SSet.opObjEquiv.symm (coherentNerveVertex Y)) := by
  rw [coherentReverseCompositionBase, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, coherentReverseHomInterval_zero, SSet.comp_const]

/-- 元の底の全区間の終点は、同じ元の始域対象。 -/
lemma coherentReverseCompositionBase_one :
    prismEndpoint 1 _ ≫ coherentReverseCompositionBase X Y Z =
      SSet.const (SSet.opObjEquiv.symm (coherentNerveVertex X)) := by
  rw [coherentReverseCompositionBase, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, coherentReverseHomInterval_one, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2

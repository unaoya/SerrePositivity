module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveCoconePrism

/-!
概要：混合宇宙の実余錐 join は、指定された元の余錐頂点を厳密に回収する。
方針：同じ Hom 持ち上げの余錐の終端を取り、元の down の頂点評価へ戻す。
規約：点射全体の等式。使われ方：通常 augmentation の dg nerve 値余錐の固定条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.MixedNerve
open SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial
variable {I C : Type (u + 1)} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

lemma coconeJoin_inr (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve I) (Δ[0] : SSet.{u + 1}) ≫ coconeJoin c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c.pt := by
  rw [coconeJoin, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_point]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  change (down C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp c.pt)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.pt
  apply ComposableArrows.ext₀
  rfl

end SerrePositivity.EInfinity.FrameHom.MixedNerve

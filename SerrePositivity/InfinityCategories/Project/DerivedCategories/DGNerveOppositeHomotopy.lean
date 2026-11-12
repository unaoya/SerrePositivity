module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SimplicialHomotopyOpposite
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeFunctor
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-!
概要：実 dg nerve 関手の全ホモトピーを、反対 dg 圏の元の実関手へ戻す。
方針：実区間の反転と dg nerve の反対比較の厳密自然性を合成する。
規約：同じ実両端を回収する。使われ方：普遍余単位の比較 cochain の方向反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 同じ実全関手ホモトピーを、反対 dg nerve の実両端へ移す。 -/
def dgNerveOppositeHomotopy (F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F.op) := by
  let eC := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C
  let eE := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R E
  let H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H) eE.hom) eC.inv
  refine { h := H'.h, h₀ := H'.h₀.trans ?_, h₁ := H'.h₁.trans ?_, rel := H'.rel }
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C).inv ≫ opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R E).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G.op
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C).inv ≫ opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R E).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F.op
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

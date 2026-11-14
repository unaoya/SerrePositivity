module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTransIso
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
/-!
概要：全 Hom 自然な双加群の実同型を、同じ dg 関手の nerve 上の全関手同型へ送る。
方針：閉零成分と全 Hom 鎖写像の可換性から、同じ厳密 dg 自然変換を作る。
規約：次数零だけの通常自然性では代用しない。使われ方：tensor の実単位と合成の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ全 Hom 自然な双加群射は、同じ成分の厳密 dg 自然変換。 -/
def dgBimoduleMapStrictNatTrans {M N : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C} (a : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (BimoduleCategory.underlying R E C M).toFunctor
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C N).toFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R E a.val a.property
/-- 双加群の同じ全 Hom 自然同型が与える、元の dg nerve 写像の全関手同型。 -/
def dgBimoduleIsoNerve {M N : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C} (e : M ≅ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleCategory.underlying R E C M).toFunctor)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleCategory.underlying R E C N).toFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R E (dgBimoduleMapStrictNatTrans R E C e.hom)
    e.hom.val (fun _ => rfl) (fun x =>
      inferInstanceAs (IsIso ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R E C x).map e.hom)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCompositionIsoComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTransIso

/-!
概要：元の graph 延長の合成比較を、実 dg nerve の関手圏での同型へ移す。
方針：厳密比較の閉零成分を元の通常同型へ同定し、全点で可逆な実ホモトピーを使う。
規約：実延長の全 Hom と実 nerve を保持。使われ方：Perf の合成同型と値の塔。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D E T : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R T] [Small.{u} T] (F : DGFunctor R D E) (G : DGFunctor R E T)

/-- 元の厳密 dg 合成比較のホモトピーから得る、実 dg nerve の関手同型。 -/
def dgExtensionCompositionNerveIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgModuleExtension R D E F).comp (dgModuleExtension R E T G)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension R D T (F.comp G))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R T (dgExtensionCompositionStrict R D E T F G)
    (fun M => (dgExtensionCompositionIso R D E T F G).hom.app
      (ForgetEnrichment.of (Complex R) M))
    (dgExtensionCompositionStrict_app_eq R D E T F G) (fun _ => inferInstance)

/-- 元の二つの nerve 関手の合成から、合成 dg 関手に沿う元の延長への実同型。 -/
def dgExtensionCompositionInfinityIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension R D E F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension R E T G))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension R D T (F.comp G))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact dgExtensionCompositionNerveIso R D E T F G

end SerrePositivity.KST.LocalizingInvariants

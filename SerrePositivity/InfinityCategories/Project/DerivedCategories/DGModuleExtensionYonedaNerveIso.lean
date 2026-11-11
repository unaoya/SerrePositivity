module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTransIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleExtensionYonedaStrict

/-! # 延長と Yoneda の native nerve の実関手同型

概要：加群延長後の Yoneda と対象像の Yoneda は実関手圏で同型。
方針：共通宇宙の始域で全 Hom 自然な実加群同型族を使う。
規約：辺や対象ごとの比較だけで済ませない。使われ方：dg 関手の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 共通宇宙の始域における延長・Yoneda 比較の実関手同型。 -/
def dgModuleExtensionYonedaNerveIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).comp (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension A D E F))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        (F.comp (_root_.SerrePositivity.DifferentialGraded.dgYoneda A E)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans A E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionYonedaLiftedStrict A D E F)
    (fun x => (_root_.SerrePositivity.DifferentialGraded.dgModuleExtensionRepresentableIso A D E F x.label.down).hom)
    (fun _ => rfl) (fun _ => inferInstance)

/-- 始域を持ち上げた Yoneda の後で、実際の加群延長を適用する表示。 -/
def dgModuleExtensionYonedaCompositeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        (dgYoneda A D)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension A D E F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        (F.comp (_root_.SerrePositivity.DifferentialGraded.dgYoneda A E)))) := by
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D)).comp
      (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension A D E F) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
      ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).comp (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension A D E F)) := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex A) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, Category.assoc, eqToHom_refl, Category.comp_id]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, he]
  exact dgModuleExtensionYonedaNerveIso A D E F

end SerrePositivity.InfinityCategories.Project.DerivedCategories

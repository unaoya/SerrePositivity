module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoTwoStepSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoPrecompNaturalitySquare
/-!
概要：同じ指定入力逆・出力比較を用いる元の cell 模型比較全体の自然性を回収する。
方針：元の出力比較の逆四角形を前合成し、元の入力比較の四角形へ接続する。
規約：原 kernel の平坦性は不要。使われ方：canonical cell 模型の射作用の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
lemma functorIso_model_hom_naturality_transfer
    {X U Z : SSet.{u}} (s : X ⟶ U) {K0 K1 : X ⟶ Z} {A0 A1 B0 B1 : U ⟶ Z}
    (c0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K0 (s ≫ A0)) (c1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K1 (s ≫ A1))
    (t0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso B0 A0) (t1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso B1 A1)
    (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom K0 K1) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom A0 A1) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom B0 B1)
    (hc : c0.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp A0 A1 s a = d ≫ c1.hom)
    (ht : t0.hom ≫ a = b ≫ t1.hom) :
    (c0 ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp t0.symm s).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp B0 B1 s b =
      d ≫ (c1 ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp t1.symm s).hom := by
  have hi : t0.inv ≫ b = a ≫ t1.inv := by
    apply (Iso.inv_comp_eq t0).2
    simpa only [Category.assoc] using ((Iso.comp_inv_eq t1).2 ht).symm
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_iso_square_forward t0.symm t1.symm a b s hi
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_trans_hom_square c0 c1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp t0.symm s)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp t1.symm s) d (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp A0 A1 s a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp B0 B1 s b) hc hp
end SerrePositivity.InfinityCategories.Project.DerivedCategories

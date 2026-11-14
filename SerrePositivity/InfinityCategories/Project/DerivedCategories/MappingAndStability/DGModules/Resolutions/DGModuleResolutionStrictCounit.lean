module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionSection
/-!
概要：実 dg 分解同値の指定余単位を厳密切断の等式へ同定する。
方針：指定された同じ比較と端点等式を保って全関手射を比較する。
規約：元の指定同型を変更しない。使われ方：実 augmentation と入力比較の正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 実分解同値の指定余単位は、同じ厳密切断の等式から得る同型そのものである。 -/
lemma dgModuleFunctorResolutionSourceNerveEquivalence_invHomIso :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).invHomIso =
      eqToIso (congrArg (fun m => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom R C E F)) := by
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories

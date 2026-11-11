module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColimit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.StrictComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Diagram

/-!
概要：B の全加群 dg nerve の bar 図式を、正本の実導来図式へ接続する。
方針：同じ全 dg Hom を保つ閉零ラベルを付け、指定された実分解関手へ送る。
規約：頂点だけでなく元の strict 図式の全単体上の一致を要求する。
使われ方：native bar 余錐の実導来像と C1 の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

def dgBarRightModuleRelabel : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) where
  obj M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

def dgBarRightModuleDerived :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgBarRightModuleRelabel R D) ≫ dgConeModuleDerived R D

lemma dgBarRightModuleDerived_strictDiagram {J : Type u} [Category J]
    (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F ≫ dgBarRightModuleDerived R D =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram R D F := by
  rfl

def dgKappaStrictDerivedBarCocone {J : Type u} [Category J]
    (F : J ⥤ ModuleCategory R D) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram R D F) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)).val ≫ dgBarRightModuleDerived R D,
    by rw [← Category.assoc,
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)).property, dgBarRightModuleDerived_strictDiagram]⟩

lemma dgKappaStrictDerivedBarCocone_vertex {J : Type u} [Category J]
    (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    (dgKappaStrictDerivedBarCocone R D F).vertex =
      dgConeModuleDerivedVertex R D
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictNormalizedModule R D F)) := by
  change (dgBarRightModuleDerived R D).app _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)).vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

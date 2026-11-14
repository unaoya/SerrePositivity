module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGProjectiveAugmentationHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelIdentityInfinity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery
/-!
概要：元の指定導来対角単位の実包含後の射を回収する。
方針：指定逆像の回収式と射影的出力比較の同じ augmentation を使う。
規約：元の単位を変更しない。使われ方：K-flat 上の通常単位との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
private lemma unit_mp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (c : γ) :
    HEq (Eq.mp h a) c ↔ HEq a c := by
  cases h
  rfl
private lemma unit_mpr_heq_iff {α β γ : Sort u} (h : α = β) (a : β) (c : γ) :
    HEq (Eq.mpr h a) c ↔ HEq a c := by
  cases h
  rfl
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の指定導来対角単位は、実包含後に同じ augmentation と生の co-Yoneda 単位の経路。 -/
lemma dgKernelDerivedInfinity_identityIso_inclusion_hom :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))).hom =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) D
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D D (Bimodule.diagonal R D)))) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))).hom := by
  dsimp -zeta only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso]
  extract_lets I e1 e2 H
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D
  have hi : HEq H (e1 ≪≫ e2) := by
    simp only [H, unit_mp_heq_iff, unit_mpr_heq_iff]
    rfl
  have hp := hf.preimageFunctorIso_postcomp H
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq ((hf.preimageFunctorIso H).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I))
    (e1 ≪≫ e2) rfl rfl ((heq_of_eq hp).trans hi)
  have hc := congrArg (fun m => m ≫ e2.hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso_hom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D D (Bimodule.diagonal R D))
      (fun M => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentity_tensor_projective R D M.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M)))
  exact (eq_of_heq hh).trans hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveAugmentationHom
public import SerrePositivity.InfinityCategories.Derived.DGKernelIdentityInfinity
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulIsoRecovery
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
private lemma unit_mp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (c : γ) :
    HEq (Eq.mp h a) c ↔ HEq a c := by
  cases h
  rfl
private lemma unit_mpr_heq_iff {α β γ : Sort u} (h : α = β) (a : β) (c : γ) :
    HEq (Eq.mpr h a) c ↔ HEq a c := by
  cases h
  rfl
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の指定導来対角単位は、実包含後に同じ augmentation と生の co-Yoneda 単位の経路。 -/
lemma dgKernelDerivedInfinity_identityIso_inclusion_hom :
    ((dgKernelDerivedInfinity_identityIso R D).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)))).hom =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgModuleResolvedAugmentationHomotopy R (SemifreeDGModules R D) D
        (dgSemifreeKernelModuleDG R D D (Bimodule.diagonal R D)))) ≫
      ((dgKernelIdentityNerveIso R D).precomp
        (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)))).hom := by
  dsimp -zeta only [dgKernelDerivedInfinity_identityIso]
  extract_lets I e1 e2 H
  have hf := dgSemifreeModulesInclusion_isFullyFaithful R D
  have hi : HEq H (e1 ≪≫ e2) := by
    simp only [H, unit_mp_heq_iff, unit_mpr_heq_iff]
    rfl
  have hp := hf.preimageFunctorIso_postcomp H
  have hh := functorIso_hom_heq ((hf.preimageFunctorIso H).postcomp (dgNerve.map I))
    (e1 ≪≫ e2) rfl rfl ((heq_of_eq hp).trans hi)
  have hc := congrArg (fun m => m ≫ e2.hom)
    (dgModuleResolvedInfinity_inclusionIso_hom R (SemifreeDGModules R D) D
      (dgSemifreeKernelModuleDG R D D (Bimodule.diagonal R D))
      (fun M => dgKernelIdentity_tensor_projective R D M.val (dgSemifreeModule_isProjective R D M)))
  exact (eq_of_heq hh).trans hc
end SerrePositivity.InfinityCategories

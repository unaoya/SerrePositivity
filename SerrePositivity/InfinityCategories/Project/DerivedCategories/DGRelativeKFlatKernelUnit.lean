module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelIdentityInfinity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery
/-!
概要：通常 K-flat kernel 作用の対角単位を、元の実 co-Yoneda 単位から回収する。
方針：元の生の nerve の指定単位を、完全充満な実包含を通じて持ち上げる。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat の単位・合成 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 同じ通常対角 kernel の K-flat 作用は、元の co-Yoneda 単位によって恒等と同型。 -/
def dgRelativeKFlatKernelIdentityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D)) := by
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D)
        (Bimodule.diagonal_rightRelativeKFlat R D) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)
      ((𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, Category.id_comp]
    simpa only [Category.comp_id] using!
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R D)).preimageFunctorIso e
/-- K-flat の指定単位は、実包含後に元の co-Yoneda 単位の同じ値を回収する。 -/
lemma dgRelativeKFlatKernelIdentityIso_inclusion_heq :
    HEq ((dgRelativeKFlatKernelIdentityIso R D).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)) := by
  dsimp -zeta only [dgRelativeKFlatKernelIdentityIso]
  extract_lets e
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R D)
  have h := hf.preimageFunctorIso_postcomp e
  apply (heq_of_eq h).trans
  simp only [e, Eq.mpr]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories

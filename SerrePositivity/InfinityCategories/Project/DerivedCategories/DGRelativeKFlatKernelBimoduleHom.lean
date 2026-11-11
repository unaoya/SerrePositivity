module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullyFaithfulFunctorHomRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTensorIsoNerveAlgebra
/-!
概要：任意の双加群射の通常 tensor 作用を K-flat 圏へ持ち上げる。
方針：実包含による後合成の完全充満性から同じ射を回収する。
規約：可逆性を仮定しない。使われ方：ξ と合成子の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
def dgRelativeKFlatKernelBimoduleHom {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ) := by
  have ee : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion]
    exact (SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)).app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E))).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullyFaithfulPreimageFunctorHom
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R E)) ee
lemma dgRelativeKFlatKernelBimoduleHom_inclusion_heq
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) :
    HEq ((SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E))).map
        (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ))
      ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)).app
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E))).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)) := by
  dsimp -zeta only [dgRelativeKFlatKernelBimoduleHom]
  extract_lets ee
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R E)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullyFaithfulPreimageFunctorHom_postcomp hf ee
  apply (heq_of_eq h).trans
  simp only [ee, Eq.mpr]
  rfl
lemma dgRelativeKFlatKernelBimoduleHom_iso_hom
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) :
    dgRelativeKFlatKernelBimoduleHom R D E e.hom hP hQ =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).hom := by
  dsimp only [dgRelativeKFlatKernelBimoduleHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor_mapIso]
  rfl
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Derived.FullyFaithfulFunctorHomRecovery
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorIsoNerveAlgebra
/-!
概要：任意の双加群射の通常 tensor 作用を K-flat 圏へ持ち上げる。
方針：実包含による後合成の完全充満性から同じ射を回収する。
規約：可逆性を仮定しない。使われ方：ξ と合成子の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
def dgRelativeKFlatKernelBimoduleHom {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    FunctorHom (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ) := by
  have ee : FunctorHom
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP ≫
        dgRelativeKFlatModuleInclusion R E)
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ ≫
        dgRelativeKFlatModuleInclusion R E) := by
    rw [dgRelativeKFlatKernelNerve_inclusion, dgRelativeKFlatKernelNerve_inclusion]
    exact (SSet.mapHomotopyCategory ((pre (dgRelativeKFlatModuleInclusion R D)).app
      (dgModuleNerve R E))).map ((dgKernelTensorFunctorHomFunctor R D E).map f)
  exact fullyFaithfulPreimageFunctorHom
    (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R E)
      (dgModuleRelativeKFlatVertex R E)) ee
lemma dgRelativeKFlatKernelBimoduleHom_inclusion_heq
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    HEq ((SSet.mapHomotopyCategory ((ihom (dgRelativeKFlatModuleNerve R D)).map
      (dgRelativeKFlatModuleInclusion R E))).map
        (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ))
      ((SSet.mapHomotopyCategory ((pre (dgRelativeKFlatModuleInclusion R D)).app
        (dgModuleNerve R E))).map ((dgKernelTensorFunctorHomFunctor R D E).map f)) := by
  dsimp -zeta only [dgRelativeKFlatKernelBimoduleHom]
  extract_lets ee
  have hf : IsFullyFaithful (dgRelativeKFlatModuleInclusion R E) :=
    isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R E) (dgModuleRelativeKFlatVertex R E)
  have h := fullyFaithfulPreimageFunctorHom_postcomp hf ee
  apply (heq_of_eq h).trans
  simp only [ee, Eq.mpr]
  rfl
lemma dgRelativeKFlatKernelBimoduleHom_iso_hom
    {P Q : BimoduleCategory R E D} (e : P ≅ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    dgRelativeKFlatKernelBimoduleHom R D E e.hom hP hQ =
      (dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).hom := by
  dsimp only [dgRelativeKFlatKernelBimoduleHom, dgRelativeKFlatKernelBimoduleIso]
  rw [← dgKernelTensorFunctorHomFunctor_mapIso]
  rfl
end
end SerrePositivity.InfinityCategories

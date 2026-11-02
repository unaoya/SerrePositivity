module

public import SerrePositivity.KTheory.G0.Functoriality
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import SerrePositivity.CommutativeAlgebra.Support.Closed

/-! # 局所化でねじれる加群の部分群

## 概要

局所化でねじれる有限加群の類が生成する部分群を定め、そのような加群が主元の台を持つこと（ある主元が加群を零化する）を示す。局所化の核がこの部分群に含まれることは格子の定理による。

## 方針

ねじれは `Module.IsTorsion'` で表し、有限生成な加群の各生成元を消す元の積を取る。

## 規約

`IsModuleSTorsion` は区切り 1-1 で `Module.IsTorsion'` に置き換えた。

## 使われ方

`G0/Localization`、KTheory/Adams。
-/

@[expose] public noncomputable section

universe u

section G0TorsionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable {R : Type u} [CommRing R]

variable (P : Submonoid R) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
/-- Classes of finite supported torsion modules generate the localization-torsion subgroup. -/
def localizationTorsionSubgroup : AddSubgroup (G0WithSupport Z) :=
  AddSubgroup.closure {x | ∃ M : SupportedFGModuleOn Z,
    Module.IsTorsion' M.obj P ∧ x = G0WithSupport.mk M}

lemma mk_mem_localizationTorsionSubgroup (M : SupportedFGModuleOn Z)
    (h : Module.IsTorsion' M.obj P) :
    G0WithSupport.mk M ∈ localizationTorsionSubgroup P Z :=
  AddSubgroup.subset_closure ⟨M, h, rfl⟩

namespace G0WithSupport
variable {P Z} {B : Type u} [CommRing B] [Algebra R B] [IsLocalization P B]

lemma localize_mk_eq_zero (W : TopologicalSpace.Closeds (PrimeSpectrum B))
    (hW : supportPullback (algebraMap R B) Z ≤ W)
    (M : SupportedFGModuleOn Z) (hM : Module.IsTorsion' M.obj P) :
    localize P Z W hW (mk M) = 0 := by
  rw [localize_mk]
  have ht : Subsingleton (B ⊗[R] M.obj) := (isTorsion'_iff_subsingleton_tensor B).mp hM
  have : Subsingleton (M.baseChange (algebraMap R B) Z W hW).obj := by
    have he : Module.compHom B (algebraMap R B) = (inferInstance : Module R B) := by
      apply Module.ext'
      intro r b
      exact algebraMap_smul B r b
    simpa +instances only [SupportedFGModuleOn.baseChange, ModuleCat.extendScalars,
      ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
      ModuleCat.RestrictScalars.obj', ModuleCat.of, he] using ht
  exact mk_of_subsingleton _

/-- All torsion relations vanish after localization; S3 will prove equality. -/
lemma localizationTorsionSubgroup_le_ker
    (W : TopologicalSpace.Closeds (PrimeSpectrum B))
    (hW : supportPullback (algebraMap R B) Z ≤ W) :
    localizationTorsionSubgroup P Z ≤ (localize P Z W hW).ker := by
  rw [localizationTorsionSubgroup, AddSubgroup.closure_le]
  rintro x ⟨M, hM, rfl⟩
  exact localize_mk_eq_zero W hW M hM
end G0WithSupport
end SerrePositivity

end G0TorsionPart

section TorsionAnnihilatorPart

namespace SerrePositivity
variable {R : Type u} [CommRing R] {P : Submonoid R}

/-- A supported torsion module has a uniformly smaller closed support. -/
lemma exists_annihilator_supportedOn
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (M : SupportedFGModuleOn Z)
    (h : Module.IsTorsion' M.obj P) :
    ∃ r ∈ P, finiteModuleSupportedOn
      (Z ⊓ supportZeroLocus (Ideal.span ({r} : Set R))) M.obj := by
  obtain ⟨r, hr, er⟩ := exists_annihilating_mem_of_isTorsion' h
  exact ⟨r, hr, M.property.1, fun p hp =>
    ⟨M.property.2 hp, module_support_subset_zeroLocus_of_annihilator r er hp⟩⟩
end SerrePositivity

end TorsionAnnihilatorPart

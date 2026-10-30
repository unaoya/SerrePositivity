module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.NilpotentModuleFiltration
public import SerrePositivity.HomologicalAlgebra.TorDimensionShift

/-! # 完全平坦性の判定と冪零イデアル

## 概要

還元の Tor の消滅から完全平坦性を判定し、冪零イデアルでは完全平坦性が平坦性と一致することを示す。

## 方針

判定は導来商の基底変換（HomologicalAlgebra）を使う。冪零の場合は Tor₁ の消滅と平坦性の局所判定。

## 規約

HomologicalAlgebra の DerivedQuotientBaseChange・RegularPrincipalTor を経由するので、`Adic/Reduction` と同じファイルにすると循環する。閉包が重い（62〜67 モジュール）ので Basic と分ける。

## 使われ方

BhattScholze の André 系（11 本）。
-/

@[expose] public noncomputable section

universe u

section CompletelyFlatCriterionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Give the ordinary quotient-tensor comparison its original quotient-ring linearity. -/
def quotientTensorReductionEquiv (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] AdicReduction I M :=
  (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- No regularity is needed once the actual residue extension is acyclic and flat. -/
theorem isCompletelyFlat_of_acyclic_flat_reduction (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hTor : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R M))
    (hFlat : Module.Flat (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of R M))) :
    IsCompletelyFlat I M := by
  intro N _ _ hN
  have hNt : Module.IsTorsionBySet R N (I : Set R) := fun {x} {r} ↦ hN r r.property x
  let := hNt.module
  let NQ := ModuleCat.of (R ⧸ I) N
  let E : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj NQ ≃ₗ[R] N :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  intro i hi
  have hz := tor_isZero_of_acyclicBaseChange_flat (Ideal.Quotient.mk I)
    (ModuleCat.of R M) hTor hFlat NQ i hi
  have hz' : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) :=
    hz.of_iso (((Tor (ModuleCat R) i).mapIso E.toModuleIso).app (ModuleCat.of R M)).symm
  have := ModuleCat.subsingleton_of_isZero hz'
  exact (torModuleComm (R := R) i M N).injective.subsingleton

/-- G3: regularity on R and M and flatness of M/aM imply the original complete flatness. -/
theorem isCompletelyFlat_principal_of_regular (a : R) (ha : IsSMulRegular R a)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsSMulRegular M a)
    (hFlat : Module.Flat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M)) :
    IsCompletelyFlat (Ideal.span {a}) M := by
  have := hFlat
  let e := (quotientScalarExtensionEquiv (Ideal.span {a}) (ModuleCat.of R M)).trans
    (quotientTensorReductionEquiv (Ideal.span {a}) M).symm
  exact isCompletelyFlat_of_acyclic_flat_reduction (Ideal.span {a}) M
    (scalarExtensionTorVanishing_principal_of_regular a ha (ModuleCat.of R M) hM)
    (Module.Flat.of_linearEquiv e)

/-- The same criterion with a faithfully flat residue gives complete faithful flatness. -/
theorem isCompletelyFaithfullyFlat_principal_of_regular (a : R) (ha : IsSMulRegular R a)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsSMulRegular M a)
    (hFlat : Module.FaithfullyFlat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M)) :
    IsCompletelyFaithfullyFlat (Ideal.span {a}) M := by
  have := hFlat
  exact ⟨isCompletelyFlat_principal_of_regular a ha M hM inferInstance, hFlat⟩

end SerrePositivity

end CompletelyFlatCriterionPart

section CompletelyFlatNilpotentPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- Extend complete flatness to all modules annihilated by a power of any ideal. -/
lemma torModule_subsingleton_of_completelyFlat_idealPowerTorsion
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M)
    (n : ℕ) (N : ModuleCat.{u} R) (hN : ∀ r ∈ I ^ n, ∀ x : N, r • x = 0)
    (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i M N) := by
  let P : ModuleCat.{u} R → Prop := fun N ↦ Subsingleton (TorModule R i M N)
  apply moduleProperty_of_idealPower_annihilated I P ?_ ?_ n N hN
  · intro N hN
    exact (isConcentratedInDegreeZero_derivedTensor_iff M N).mp (hM N hN) i hi
  · intro S hS h₁ h₃
    exact torModule_subsingleton_of_exact M S.f.hom S.g.hom
      ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) i h₁ h₃

/-- Complete flatness for a nilpotent ideal tests all modules and gives ordinary flatness. -/
lemma flat_of_completelyFlat_nilpotent (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M) :
    Module.Flat R M := by
  obtain ⟨n, hn⟩ := hNil
  have ht (N : Type u) [AddCommGroup N] [Module R N] :
      Subsingleton (TorModule R 1 M N) := by
    apply torModule_subsingleton_of_completelyFlat_idealPowerTorsion I M hM n
      (ModuleCat.of R N) ?_ 1 (by omega)
    intro r hr x
    rw [hn, Ideal.mem_bot] at hr
    rw [hr, zero_smul]
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro N N' _ _ _ _ f hf
  exact lTensor_injective_of_torModule_one M f f.range.mkQ hf f.range.mkQ_surjective
    f.exact_map_mkQ_range (ht (N' ⧸ f.range))

/-- Over a nilpotent ideal, the existing complete flatness predicate is equivalent to flatness. -/
lemma isCompletelyFlat_nilpotent_iff_flat (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (M : Type u) [AddCommGroup M] [Module R M] :
    IsCompletelyFlat I M ↔ Module.Flat R M := by
  refine ⟨flat_of_completelyFlat_nilpotent I hNil M, ?_⟩
  intro hFlat
  let hF := hFlat
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  intro i hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact torModule_subsingleton_of_flat M N j

end SerrePositivity

end CompletelyFlatNilpotentPart

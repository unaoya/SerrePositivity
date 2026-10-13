module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # 代数の標準写像の余核と係数制限

S→C の余核を S 加群として作り、R 線形な標準写像の余核と R 線形同型で比較する。
R 線形像に S の作用を直接仮定せず、S 部分加群としての像を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

/-- 代数の標準写像 S→C の、S 加群としての余核。 -/
abbrev AlgebraMapCokernel (S C : Type u) [CommRing S] [CommRing C] [Algebra S C] :=
  C ⧸ (Algebra.linearMap S C).range

variable (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]

/-- 係数制限で標準写像の像は変わらない。 -/
theorem algebraMap_range_restrictScalars :
    (Algebra.linearMap S C).range.restrictScalars R =
      (IsScalarTower.toAlgHom R S C).toLinearMap.range := by
  ext x
  rfl

/-- R 線形な標準写像の余核と、S 加群の余核の係数制限との比較。 -/
def algebraMapCokernelRestrictEquiv :
    (C ⧸ (IsScalarTower.toAlgHom R S C).toLinearMap.range) ≃ₗ[R]
      AlgebraMapCokernel S C :=
  (Submodule.quotEquivOfEq _ _ (algebraMap_range_restrictScalars R S C).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R (Algebra.linearMap S C).range)

/-- 比較は余核の代表元を保つ。 -/
@[simp] theorem algebraMapCokernelRestrictEquiv_mk (x : C) :
    algebraMapCokernelRestrictEquiv R S C (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  simp [algebraMapCokernelRestrictEquiv]

/-- R の元による零化を、S 加群としての余核へ移す。 -/
theorem algebraMapCokernel_annihilated_of_restrict (r : R)
    (h : ∀ x : C ⧸ (IsScalarTower.toAlgHom R S C).toLinearMap.range, r • x = 0) :
    ∀ x : AlgebraMapCokernel S C, r • x = 0 := by
  intro x
  obtain ⟨y, rfl⟩ := (algebraMapCokernelRestrictEquiv R S C).surjective x
  rw [← LinearEquiv.map_smul, h, map_zero]

/-- 係数制限の零化は S における像の元の零化にもなる。 -/
theorem algebraMapCokernel_annihilated_algebraMap_of_restrict (r : R)
    (h : ∀ x : C ⧸ (IsScalarTower.toAlgHom R S C).toLinearMap.range, r • x = 0) :
    ∀ x : AlgebraMapCokernel S C, algebraMap R S r • x = 0 := by
  intro x
  rw [IsScalarTower.algebraMap_smul]
  exact algebraMapCokernel_annihilated_of_restrict R S C r h x

/-- 標準写像とその実際の余核の短複体。 -/
def algebraMapCokernelShortComplex : CategoryTheory.ShortComplex (ModuleCat.{u} S) :=
  CategoryTheory.ShortComplex.moduleCatMk (Algebra.linearMap S C)
    (Algebra.linearMap S C).range.mkQ (by
      apply LinearMap.ext
      intro s
      change Submodule.Quotient.mk (algebraMap S C s) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨s, rfl⟩)

/-- 標準写像が単射なら、標準写像・余核から実際の短完全列が得られる。 -/
theorem algebraMapCokernelShortComplex_shortExact
    (hinj : Function.Injective (algebraMap S C)) :
    (algebraMapCokernelShortComplex S C).ShortExact := by
  let sc := algebraMapCokernelShortComplex S C
  have : CategoryTheory.Mono sc.f :=
    (ModuleCat.mono_iff_injective _).mpr hinj
  have : CategoryTheory.Epi sc.g :=
    (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  refine ⟨?_⟩
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact (Submodule.ker_mkQ _).symm

end SerrePositivity

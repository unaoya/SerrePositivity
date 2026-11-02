module

public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # Prop 2.4.7：実局所自由比較から有限自由加群への元の写像

有限表示性で元の局所同型の分母を払い、既存 Claim 2.4.8 へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R M : Type u} [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-- 元の局所自由同型の一つの分母を払い、その同型を保つ実写像と錐零化を得る。
rank 0・零環・g の零因子性を排除しない。 -/
theorem prop247_exists_finiteFree_comparison_of_tensor_equiv
    (g : R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization (.powers g) A]
    (r : ℕ) (e : A ⊗[R] M ≃ₗ[A] (Fin r → A)) :
    ∃ (k : ℕ) (u : M →ₗ[R] (Fin r → R)),
      (∀ x : M, ∀ i : Fin r, algebraMap R A (u x i) =
        (algebraMap R A g) ^ k * e (1 ⊗ₜ[R] x) i) ∧
      Function.Bijective (awayModuleMap g u) ∧
      ∃ q : ℕ, moduleMapConeScalar R u (g ^ q) = 0 ∧
        (∀ x : u.ker, g ^ q • x = 0) ∧
        (∀ y : (Fin r → R) ⧸ u.range, g ^ q • y = 0) := by
  let S := Submonoid.powers g
  let ιM := LocalizedModule.mkLinearMap S M
  let ιF := LocalizedModule.mkLinearMap S (Fin r → R)
  let j : (Fin r → R) →ₗ[R] (Fin r → A) :=
    LinearMap.pi (fun i => (Algebra.linearMap R A).comp (LinearMap.proj i))
  have : IsLocalizedModule S j := IsLocalizedModule.pi S (fun _ : Fin r => Algebra.linearMap R A)
  let eF := IsLocalizedModule.linearEquiv S ιF j
  let jM := TensorProduct.mk R A M (1 : A)
  have : IsLocalizedModule S jM := IsLocalization.tensorProduct_isLocalizedModule S A
  let eM := IsLocalizedModule.linearEquiv S ιM jM
  let e' := eM.trans ((e.restrictScalars R).trans eF.symm)
  obtain ⟨k, u, hu, hbij⟩ := exists_away_comparison_of_finitePresentation g e'
  refine ⟨k, u, ?_, hbij, finiteFreeConeIsogeny_with_annihilators R g r u hbij⟩
  intro x i
  have hx := LinearMap.congr_fun hu (ιM x)
  change awayModuleMap g u (ιM x) = g ^ k • e' (ιM x) at hx
  rw [awayModuleMap, IsLocalizedModule.map_apply] at hx
  have hh := congrArg (fun z => eF z) hx
  have hm : eM (ιM x) = (1 : A) ⊗ₜ[R] x :=
    IsLocalizedModule.linearEquiv_apply S ιM jM x
  have hz : j (u x) = g ^ k • e (1 ⊗ₜ[R] x) := by
    change eF (ιF (u x)) = eF ((g ^ k : R) • e' (ιM x)) at hh
    rw [show eF (ιF (u x)) = j (u x) from
      IsLocalizedModule.linearEquiv_apply S ιF j (u x), map_smul] at hh
    calc
      j (u x) = g ^ k • eF (e' (ιM x)) := hh
      _ = g ^ k • eF (eF.symm (e (eM (ιM x)))) := rfl
      _ = g ^ k • e (eM (ιM x)) :=
        congrArg (fun z => (g ^ k : R) • z) (eF.apply_symm_apply _)
      _ = g ^ k • e (1 ⊗ₜ[R] x) := by rw [hm]
  have hi := congrFun hz i
  change algebraMap R A (u x i) = (g ^ k : R) • e (1 ⊗ₜ[R] x) i at hi
  simpa only [Algebra.smul_def, map_pow] using hi

end SerrePositivity.CLMST

module

public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge
public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# 完備 de Rham 微分の Leibniz 則

## 概要
完備微分は完備外積について Leibniz 則を満たす。

## 方針
完備化単位上の公式を、完備な標的への線形写像の一意性で延長する。

## 規約
線形性は元の係数環上。符号は左の形式の次数で決める。

## 使われ方
完備 de Rham 複体の積。
-/

public section
noncomputable section

universe u

open CategoryTheory
open SerrePositivity.DerivedCompletion
open scoped TensorProduct

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ)
local notation "P" => Poly k T
local notation "Q" => completedPoly k T p
local notation "E[" i "]" => (⋀[k]^i (T → k))

private def representative (x : ℕ → P) : Q :=
  (principalCompletionH0Equiv P (p : P)).symm (principalReflectionMk P (p : P) x)

private theorem representative_step (x : ℕ → P) :
    representative k T p x =
      algebraMap P Q (x 0) + (p : ℕ) • representative k T p (sequenceTail P x) := by
  let e := principalCompletionH0Equiv P (p : P)
  change e.symm (principalReflectionMk P (p : P) x) = _
  rw [principalReflectionMk_decomposition, map_add, map_smul, map_smul, Nat.cast_smul_eq_nsmul]
  congr 1
  apply e.injective
  rw [map_smul, LinearEquiv.apply_symm_apply]
  change x 0 • principalReflectionUnit P (p : P) = e (principalCompletionUnitRingHom P (p : P) (x 0))
  simp only [e, principalCompletionUnitRingHom_apply, principalCompletionH0Equiv_unit,
    principalReflectionUnit, ← map_smul, ← map_smul, smul_eq_mul, mul_one]

private theorem completedPoly_linearMap_ext {M : Type u} [AddCommGroup M] [Module k M]
    (hM : IsModuleComplete k (p : k) (ModuleCat.of k M)) {f g : Q →ₗ[k] M}
    (h : ∀ x : P, f (algebraMap P Q x) = g (algebraMap P Q x)) : f = g := by
  apply sub_eq_zero.mp
  let F := f - g
  have hF (x : P) : F (algebraMap P Q x) = 0 := sub_eq_zero.mpr (h x)
  apply LinearMap.ext
  intro z
  let e := principalCompletionH0Equiv P (p : P)
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (principalReflectionRelation P (p : P)).range (e z)
  have hz : z = representative k T p x := by
    apply e.injective
    exact hx.symm.trans (e.apply_symm_apply _).symm
  rw [hz]
  let y : ℕ → M := fun n => F (representative k T p (fun j => x (n + j)))
  have hy : adicRecurrenceMap (p : k) y = 0 := by
    funext n
    have ht : sequenceTail P (fun j => x (n + j)) = (fun j => x ((n + 1) + j)) := by
      funext j
      change x (n + (j + 1)) = x ((n + 1) + j)
      congr 1
      omega
    have hs := congrArg F (representative_step k T p (fun j => x (n + j)))
    rw [ht, map_add, map_nsmul, hF, zero_add] at hs
    change y n - (p : k) • y (n + 1) = 0
    rw [Nat.cast_smul_eq_nsmul]
    exact sub_eq_zero.mpr hs
  have he := ((isModuleComplete_iff_recurrence_bijective k (p : k) (ModuleCat.of k M)).mp hM).injective
    (hy.trans (map_zero _).symm)
  change F (representative k T p x) = 0
  simpa [y] using congrFun he 0

private def coeffEquiv (i : ℕ) : completedForms k T p i ≃ₗ[k] Q ⊗[k] E[i] :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange k P Q Q E[i]).restrictScalars k

private theorem completedForms_complete (i : ℕ) :
    IsModuleComplete k (p : k) (ModuleCat.of k (completedForms k T p i)) := by
  classical
  let : LinearOrder T := linearOrderOfSTO WellOrderingRel
  let b := (Pi.basisFun k T).exteriorPower i
  let e := ((coeffEquiv k T p i).trans
    ((TensorProduct.equivFinsuppOfBasisRight b).trans
      (Finsupp.linearEquivFunOnFinite k Q _)))
  let e' := LinearEquiv.funCongrLeft k Q (Fintype.equivFin (Set.powersetCard T i)).symm
  let I := Fin (Fintype.card (Set.powersetCard T i))
  apply isModuleComplete_of_linearEquiv k (p : k) (ModuleCat.of k (I → Q)) _
    (e.trans e').symm
  have hQ : IsModuleComplete k (p : k) (ModuleCat.of k Q) := by
    apply (isModuleComplete_algebraMap_iff k P (p : k) Q).mp
    rw [map_natCast]
    exact principalCompletionH0_isModuleComplete P (p : P)
  exact isModuleComplete_pi k (p : k) (fun _ : I => ModuleCat.of k Q) (fun _ => hQ)

private theorem completedForms_linearMap_ext {M : Type u} [AddCommGroup M] [Module k M]
    (hM : IsModuleComplete k (p : k) (ModuleCat.of k M)) {i : ℕ}
    {f g : completedForms k T p i →ₗ[k] M}
    (h : ∀ x : forms k T i, f (completedFormsUnit k T p i x) =
      g (completedFormsUnit k T p i x)) : f = g := by
  apply LinearMap.ext
  intro z
  let e := coeffEquiv k T p i
  obtain ⟨w, rfl⟩ := e.symm.surjective z
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x v =>
    let j : Q →ₗ[k] completedForms k T p i :=
      e.symm.toLinearMap ∘ₗ (TensorProduct.mk k Q E[i]).flip v
    have hfg : f.comp j = g.comp j := by
      apply completedPoly_linearMap_ext k T p hM
      intro r
      have he : e (completedFormsUnit k T p i (r ⊗ₜ[k] v)) = algebraMap P Q r ⊗ₜ[k] v := by
        change TensorProduct.AlgebraTensorModule.cancelBaseChange k P Q Q E[i]
          (1 ⊗ₜ[P] (r ⊗ₜ[k] v)) = _
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
      have hj : j (algebraMap P Q r) = completedFormsUnit k T p i (r ⊗ₜ[k] v) := by
        apply e.injective
        rw [he]
        exact e.apply_symm_apply _
      change f (j (algebraMap P Q r)) = g (j (algebraMap P Q r))
      rw [hj]
      exact h _
    exact LinearMap.congr_fun hfg x

private def dLinear (i : ℕ) : completedForms k T p i →ₗ[k] completedForms k T p (i + 1) :=
  { completedDeRhamD k T p i with
    map_smul' := fun a x => by
      unfold completedDeRhamD
      change completedDLinear k T p i (a • x) = a • completedDLinear k T p i x
      exact map_smul _ _ _ }

private def wedgeLinear (i j : ℕ) :
    completedForms k T p i →ₗ[k] completedForms k T p j →ₗ[k] completedForms k T p (i + j) :=
  LinearMap.mk₂ k (completedWedge k T p)
    (fun x y z => by unfold completedWedge; simp only [map_add, LinearMap.add_apply])
    (fun a x y => by unfold completedWedge; simp only [← LinearEquiv.coe_coe, map_smul, LinearMap.map_smul_of_tower, LinearMap.smul_apply])
    (fun x y z => by unfold completedWedge; simp only [map_add])
    (fun a x y => by unfold completedWedge; simp only [← LinearEquiv.coe_coe, map_smul, LinearMap.map_smul_of_tower])

private theorem completedFormsUnit_cast {i j : ℕ} (h : i = j) (x : forms k T i) :
    completedFormsUnit k T p j (cast (congrArg (forms k T) h) x) =
      cast (congrArg (completedForms k T p) h) (completedFormsUnit k T p i x) := by
  subst j
  rfl

/-- 概要：完備多項式形式の微分は完備外積に関して符号付き Leibniz 則を満たす。
方針：完備化単位上の多項式形式での等式を、導来完備な標的への一意性で二変数に延長する。
規約：右因子を微分する項の符号は左因子の次数で決める。
使われ方：完備多項式 de Rham 複体の積。 -/
theorem completedDeRhamD_wedge {i j : ℕ} (ω : completedForms k T p i) (η : completedForms k T p j) :
    completedDeRhamD k T p (i + j) (completedWedge k T p ω η) =
      cast (congrArg (completedForms k T p) (by omega : (i + 1) + j = (i + j) + 1))
        (completedWedge k T p (completedDeRhamD k T p i ω) η) +
      (-1 : ℤ)^i • completedWedge k T p ω (completedDeRhamD k T p j η) := by
  let e : (i + 1) + j = (i + j) + 1 := by omega
  let c : completedForms k T p ((i + 1) + j) ≃ₗ[k] completedForms k T p ((i + j) + 1) :=
    LinearEquiv.cast (M := completedForms k T p) e
  let lhs := (wedgeLinear k T p i j).compr₂ (dLinear k T p (i + j))
  let rhs := ((wedgeLinear k T p (i + 1) j).compr₂ c.toLinearMap).compl₁₂
      (dLinear k T p i) LinearMap.id +
    (-1 : ℤ)^i • (wedgeLinear k T p i (j + 1)).compl₂ (dLinear k T p j)
  have hunit (a : forms k T i) (b : forms k T j) :
      lhs (completedFormsUnit k T p i a) (completedFormsUnit k T p j b) =
        rhs (completedFormsUnit k T p i a) (completedFormsUnit k T p j b) := by
    change completedDeRhamD k T p (i + j)
        (completedWedge k T p (completedFormsUnit k T p i a) (completedFormsUnit k T p j b)) =
      cast (congrArg (completedForms k T p) e)
        (completedWedge k T p (completedDeRhamD k T p i (completedFormsUnit k T p i a))
          (completedFormsUnit k T p j b)) +
      (-1 : ℤ)^i • completedWedge k T p (completedFormsUnit k T p i a)
        (completedDeRhamD k T p j (completedFormsUnit k T p j b))
    simp only [completedWedge_unit, completedDeRhamD_unit, deRhamD_wedge,
      map_add, map_zsmul, completedFormsUnit_cast k T p e]
    rfl
  have hc := completedForms_complete k T p (i + j + 1)
  have hleft (b : forms k T j) :
      lhs.flip (completedFormsUnit k T p j b) = rhs.flip (completedFormsUnit k T p j b) :=
    completedForms_linearMap_ext k T p hc (fun a => hunit a b)
  have hall : lhs ω = rhs ω :=
    completedForms_linearMap_ext k T p hc (fun b => LinearMap.congr_fun (hleft b) ω)
  exact LinearMap.congr_fun hall η

end SerrePositivity.DeRham

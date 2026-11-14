module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 標数 p の pd de Rham 列の未完備表示

## 概要
係数環で p が零のとき、完備列を未完備分冪係数の微分形式で表す。

## 方針
零元での完備化が単位同型であることと、偏微分の延長公式を使う。

## 規約
形式の基底は両側で同じ。

## 使われ方
標数 p の pd Poincaré 補題。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (hp : (p : k) = 0)

private def pdRawToTerm (n : ℕ) : pdRaw k r n ≃ₐ[k] pdTerm p k r n := by
  have h : (p : pdRaw k r n) = 0 := by
    rw [← map_natCast (algebraMap k (pdRaw k r n)), hp, map_zero]
  letI := principalCompletionCommRing (pdRaw k r n) (p : pdRaw k r n)
  let E := crystallinePrincipalCompletionOfZero (p : pdRaw k r n) h
  refine { __ := E.symm, commutes' := fun c => ?_ }
  change E.symm (algebraMap k (pdRaw k r n) c) =
    principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n)) (algebraMap k (pdRaw k r n) c)
  apply E.injective
  rw [RingEquiv.apply_symm_apply]
  exact (crystallinePrincipalCompletionOfZero_unit _ h _).symm

private theorem pdRawToTerm_eq_unit (n : ℕ) (x : pdRaw k r n) :
    pdRawToTerm p k r hp n x = principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n)) x := by
  have h : (p : pdRaw k r n) = 0 := by
    rw [← map_natCast (algebraMap k (pdRaw k r n)), hp, map_zero]
  let := principalCompletionCommRing (pdRaw k r n) (p : pdRaw k r n)
  let E := crystallinePrincipalCompletionOfZero (p : pdRaw k r n) h
  apply E.injective
  change E (E.symm x) = E (principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n)) x)
  rw [RingEquiv.apply_symm_apply]
  exact (crystallinePrincipalCompletionOfZero_unit _ h x).symm

/-- 未完備の分冪係数と頂点の外冪をテンソルした形式。 -/
abbrev pdRawForms (n : SimplexCategory) (j : ℕ) :=
  pdRaw k r n.len ⊗[k] (⋀[k]^j (((Fin r × Fin (n.len + 1)) →₀ k)))

/-- 未完備の分冪係数での列微分。 -/
def pdRawVertical (n : SimplexCategory) (j : ℕ) :
    pdRawForms k r n j →ₗ[k] pdRawForms k r n (j+1) :=
  ∑ a : pdCoordinates r n.len, TensorProduct.map
    (pdRawPartial k r n.len a) (DeRham.wedgeOne k (((Fin r × Fin (n.len + 1)) →₀ k)) j (pdCoordinateOne k r n a))

private def pdRawFormsEquiv (n : SimplexCategory) (j : ℕ) :
    pdRawForms k r n j ≃ₗ[k] (pdDeRhamColumn p k r n).X j :=
  TensorProduct.congr (pdRawToTerm p k r hp n.len).toLinearEquiv (LinearEquiv.refl k _)

private theorem pdRawFormsEquiv_tmul (n : SimplexCategory) (j : ℕ) (f : pdRaw k r n.len)
    (w : ⋀[k]^j (((Fin r × Fin (n.len + 1)) →₀ k))) :
    pdRawFormsEquiv p k r hp n j (f ⊗ₜ[k] w) =
      pdRawToTerm p k r hp n.len f ⊗ₜ[k] w := by
  exact TensorProduct.congr_tmul _ _ _ _

private theorem pdRawFormsEquiv_d (n : SimplexCategory) (j : ℕ) :
    (pdRawFormsEquiv p k r hp n (j+1)).toLinearMap.comp (pdRawVertical k r n j) =
      (pdVerticalD p k r n j).hom.comp (pdRawFormsEquiv p k r hp n j).toLinearMap := by
  apply TensorProduct.ext'
  intro f ω
  change pdRaw k r n.len at f
  change ⋀[k]^j (((Fin r × Fin (n.len + 1)) →₀ k)) at ω
  let D := ∑ a : pdCoordinates r n.len, TensorProduct.map
    (pdPartial p k r n.len a) (DeRham.wedgeOne k (((Fin r × Fin (n.len + 1)) →₀ k)) j (pdCoordinateOne k r n a))
  let E := (pdRawFormsEquiv p k r hp n (j+1)).toLinearMap
  change E (pdRawVertical k r n j (f ⊗ₜ[k] ω)) =
    D (pdRawFormsEquiv p k r hp n j (f ⊗ₜ[k] ω))
  simp only [pdRawVertical, D, LinearMap.sum_apply, TensorProduct.map_tmul, pdRawFormsEquiv_tmul,
    E, LinearEquiv.coe_coe, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pdRawToTerm_eq_unit, pdRawToTerm_eq_unit]
  congr 1
  let R := pdRaw k r n.len
  exact (principalCompletionLinearMap_unit k p (A := R) (B := R)
    (pdRawPartial k r n.len a) f).symm

include hp in
/-- 未完備列の微分の平方は零。 -/
theorem pdRawVertical_sq (n : SimplexCategory) (j : ℕ) :
    (pdRawVertical k r n (j+1)).comp (pdRawVertical k r n j) = 0 := by
  apply LinearMap.ext
  intro x
  apply (pdRawFormsEquiv p k r hp n (j+2)).injective
  rw [LinearMap.comp_apply, LinearMap.zero_apply,
    (pdRawFormsEquiv p k r hp n (j+2)).map_zero]
  have h (i : ℕ) (y : pdRawForms k r n i) :
      (pdRawFormsEquiv p k r hp n (i+1)) (pdRawVertical k r n i y) =
        (pdVerticalD p k r n i) (pdRawFormsEquiv p k r hp n i y) :=
    DFunLike.congr_fun (pdRawFormsEquiv_d p k r hp n i) y
  change (pdRawFormsEquiv p k r hp n (j+2)) (pdRawVertical k r n (j+1)
    (pdRawVertical k r n j x)) = _
  rw [h (j+1) _, h j _]
  exact ConcreteCategory.congr_hom (pdVerticalD_sq p k r n j) (pdRawFormsEquiv p k r hp n j x)

/-- 未完備分冪係数上の de Rham 列。 -/
@[expose] def pdRawDeRhamColumn (n : SimplexCategory) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun j => ModuleCat.of k (pdRawForms k r n j))
    (fun j => ModuleCat.ofHom (pdRawVertical k r n j))
    (fun j => ModuleCat.hom_ext (pdRawVertical_sq p k r hp n j))

/-- 係数環で p が零なら、完備列と未完備列は同型。 -/
def pdRawDeRhamColumnIso (n : SimplexCategory) :
    pdRawDeRhamColumn p k r hp n ≅ pdDeRhamColumn p k r n :=
  HomologicalComplex.Hom.isoOfComponents (fun j => (pdRawFormsEquiv p k r hp n j).toModuleIso)
    (by
      intro i j hij
      have h : i+1 = j := hij
      subst j
      dsimp only [pdRawDeRhamColumn, pdDeRhamColumn, CochainComplex.of]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      exact ModuleCat.hom_ext (pdRawFormsEquiv_d p k r hp n i).symm)

end SerrePositivity.BhattScholze.Prismatic

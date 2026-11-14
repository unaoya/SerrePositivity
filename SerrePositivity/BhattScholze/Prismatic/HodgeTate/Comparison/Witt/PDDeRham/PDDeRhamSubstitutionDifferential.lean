module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionDegreeZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionDegreeZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 完備分冪 de Rham の代入と微分

## 概要
完備分冪形式の多項式代入は、すべての次数で微分と可換である。

## 方針
頂点変数の微分が 1 形式の基底であることを使う。
外積の保存と Leibniz 則で、次数 0 と完全な 1 形式から全次数へ延ばす。

## 規約
固定した余単体次数で微分との可換性を示す。

## 使われ方
BS 著者版 Theorem 6.4 の完備分冪 de Rham の厳密な自然性。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham SerrePositivity.DerivedCompletion
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q') (n : ℕ)

local notation "SourceRing" => pdTerm p k Q.n n
local notation "SourceCopy" => ((Fin Q.n × Fin (n + 1)) →₀ k)
private abbrev rowModule (r j : ℕ) : ModuleCat.{u} k := (pdRow p k r j).obj ⦋n⦌
local notation "Fs" j => rowModule (k := k) p n Q.n j
local notation "Ft" j => rowModule (k := k) p n Q'.n j
local notation "e" => substituteRowForms p γ hk hr f n
local notation "Ds" => pdVerticalD p k Q.n ⦋n⦌
local notation "Dt" => pdVerticalD p k Q'.n ⦋n⦌

private def CommutesD (i : ℕ) (x : Fs i) : Prop :=
  Dt i (e i x) = e (i + 1) (Ds i x)

private theorem commutesD_cast {i j : ℕ} (h : i = j) (x : Fs i)
    (hx : CommutesD p γ hk hr f n i x) :
    CommutesD p γ hk hr f n j (cast (congrArg (fun j => (Fs j : Type u)) h) x) := by
  subst j
  exact hx

private theorem substitute_cast {i j : ℕ} (h : i = j) (x : Fs i) :
    e j (cast (congrArg (fun j => (Fs j : Type u)) h) x) =
      cast (congrArg (fun j => (Ft j : Type u)) h) (e i x) := by
  subst j
  rfl

private theorem commutesD_wedge {i j : ℕ} (x : Fs i) (y : Fs j)
    (hx : CommutesD p γ hk hr f n i x) (hy : CommutesD p γ hk hr f n j y) :
    CommutesD p γ hk hr f n (i + j) (pdWedge p k Q.n ⦋n⦌ i j x y) := by
  unfold CommutesD at *
  rw [substituteForms_wedge, pdVerticalD_wedge, pdVerticalD_wedge, map_add, map_zsmul,
    substitute_cast, substituteForms_wedge]
  have h := substituteForms_wedge p γ hk hr f n i (j + 1) x (Ds j y)
  change e (i + j + 1) (pdWedge p k Q.n ⦋n⦌ i (j + 1) x (Ds j y)) = _ at h
  rw [h, hx, hy]
  all_goals omega

omit [Fact p.Prime] in
private theorem d_vertex (j : Fin Q.n) (i : Fin (n + 1)) :
    let U := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k Q.n n))
    Ds 0 (U (copy k Q.n ⦋n⦌ j i) ⊗ₜ[k] (exteriorPower.zeroEquiv k SourceCopy).symm 1) =
      (1 : SourceRing) ⊗ₜ[k] (exteriorPower.oneEquiv k SourceCopy).symm (Finsupp.single (j,i) 1) := by
  dsimp only
  rw [d_zero_tmul]
  let v : SourceCopy := Finsupp.single (j,i) 1
  let b := pdCoordinateBasis k Q.n ⦋n⦌
  let E := (exteriorPower.oneEquiv k SourceCopy).symm
  have hE (a : pdCoordinates Q.n n) : pdCoordinateOne k Q.n ⦋n⦌ a = E (b a) := by
    rw [pdCoordinateBasis_apply]
    rfl
  have hB (a : pdCoordinates Q.n n) : b.repr v a =
      copyToCoordinate k Q.n ⦋n⦌ v a := rfl
  change (∑ a : pdCoordinates Q.n n, pdPartial p k Q.n n a _ ⊗ₜ[k]
    pdCoordinateOne k Q.n ⦋n⦌ a) = (1 : SourceRing) ⊗ₜ[k] E v
  rw [← b.sum_repr v, map_sum, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pdPartial, principalCompletionLinearMap_unit, copy_partial, hE, ← hB, map_smul]
  change (algebraMap k SourceRing (b.repr v a)) ⊗ₜ[k] E (b a) =
    (1 : SourceRing) ⊗ₜ[k] (b.repr v a • E (b a))
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

private theorem commutesD_image {j : ℕ} (x : Fs j)
    (h : CommutesD p γ hk hr f n j x) :
    CommutesD p γ hk hr f n (j + 1) (Ds j x) := by
  unfold CommutesD at *
  rw [← h]
  have hS := ConcreteCategory.congr_hom (pdVerticalD_sq p k Q.n ⦋n⦌ j) x
  have hT := ConcreteCategory.congr_hom (pdVerticalD_sq p k Q'.n ⦋n⦌ j) (e j x)
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hS hT
  rw [hS, map_zero]
  exact hT

private theorem commutesD_degreeZero (x : Fs 0) : CommutesD p γ hk hr f n 0 x :=
  ConcreteCategory.congr_hom (substituteRowForms_d_zero p γ hk hr f n) x

private theorem commutesD_one (v : SourceCopy) :
    CommutesD p γ hk hr f n 1
      ((1 : SourceRing) ⊗ₜ[k] (exteriorPower.oneEquiv k SourceCopy).symm v) := by
  let E := (exteriorPower.oneEquiv k SourceCopy).symm
  let l : SourceCopy →ₗ[k] Fs 1 := (TensorProduct.mk k SourceRing _ 1).comp E.toLinearMap
  let F := (Dt 1).hom.comp ((e 1).hom.comp l)
  let G := (e 2).hom.comp ((Ds 1).hom.comp l)
  have h : F = G := by
    apply (Finsupp.basisSingleOne (R := k)).ext
    rintro ⟨j,i⟩
    change CommutesD p γ hk hr f n 1 ((1 : SourceRing) ⊗ₜ[k] E (Finsupp.single (j,i) 1))
    rw [← d_vertex p n j i]
    exact commutesD_image p γ hk hr f n _ (commutesD_degreeZero p γ hk hr f n _)
  exact DFunLike.congr_fun h v

private theorem commutesD_tmul_ιMulti (x : SourceRing) (j : ℕ) (v : Fin j → SourceCopy) :
    CommutesD p γ hk hr f n j (x ⊗ₜ[k] exteriorPower.ιMulti k j v) := by
  induction j with
  | zero => exact commutesD_degreeZero p γ hk hr f n _
  | succ j ih =>
    let E := (exteriorPower.oneEquiv k SourceCopy).symm
    let a : Fs 1 := (1 : SourceRing) ⊗ₜ[k] E (v 0)
    let z : Fs j := x ⊗ₜ[k] exteriorPower.ιMulti k j (fun i => v i.succ)
    have h := commutesD_cast p γ hk hr f n (Nat.add_comm 1 j) _
      (commutesD_wedge p γ hk hr f n a z
        (commutesD_one p γ hk hr f n (v 0)) (ih (fun i => v i.succ)))
    have hv : (x ⊗ₜ[k] exteriorPower.ιMulti k (j + 1) v : Fs (j + 1)) =
        cast (congrArg (fun t => (Fs t : Type u)) (Nat.add_comm 1 j))
          (pdWedge p k Q.n ⦋n⦌ 1 j a z) := by
      apply (SerrePositivity.KST.DerivedBlowup.exteriorBaseChangeDegreeInclusion_injective
        (R := k) (S := SourceRing) (M := SourceCopy) (j + 1))
      rw [show ∀ (i t : ℕ) (ht : i = t) (y : Fs i),
        SerrePositivity.KST.DerivedBlowup.exteriorBaseChangeDegreeInclusion t
          (cast (congrArg (fun t => (Fs t : Type u)) ht) y) =
        SerrePositivity.KST.DerivedBlowup.exteriorBaseChangeDegreeInclusion i y by
          intro i t ht y
          subst t
          rfl]
      rw [inclusion_wedge]
      change x ⊗ₜ[k] (ExteriorAlgebra.ιMulti k (j + 1) v) =
        ((1 : SourceRing) ⊗ₜ[k] (E (v 0)).val) *
          (x ⊗ₜ[k] ExteriorAlgebra.ιMulti k j (fun i => v i.succ))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ExteriorAlgebra.ιMulti_succ_apply]
      congr 1
      simp [E, exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti, ExteriorAlgebra.ιMulti_apply,
        Matrix.vecTail]
      all_goals omega
    rw [hv]
    exact h

/-- 固定した余単体次数で、多項式代入は全次数の完備分冪 de Rham 微分と可換。 -/
theorem substituteRowForms_d (j : ℕ) :
    e j ≫ Dt j = Ds j ≫ e (j + 1) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x w
  let F := (Dt j).hom.comp ((e j).hom.comp (TensorProduct.mk k SourceRing _ x))
  let G := (e (j + 1)).hom.comp ((Ds j).hom.comp (TensorProduct.mk k SourceRing _ x))
  have h : F = G := by
    apply LinearMap.ext_on (s := Set.range (exteriorPower.ιMulti k j : (Fin j → SourceCopy) → _))
    · exact exteriorPower.ιMulti_span k j SourceCopy
    · rintro _ ⟨v,rfl⟩
      exact commutesD_tmul_ιMulti p γ hk hr f n x j v
  exact DFunLike.congr_fun h w

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

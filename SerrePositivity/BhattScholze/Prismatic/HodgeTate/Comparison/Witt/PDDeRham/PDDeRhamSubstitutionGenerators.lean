module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionWedge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionWedge
import all SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeContraction

/-!
# 完備分冪 de Rham の代入の生成元公式

## 概要
完備係数と頂点の 1 形式上の代入を計算する。

## 方針
総外積への包含と外積の普遍写像の生成元公式を使う。

## 規約
1 形式は頂点変数を微分したものに対応する。

## 使われ方
BS 著者版 Theorem 6.4 の代入と微分の可換性。
-/

public noncomputable section

open CategoryTheory
open SerrePositivity.KST.DerivedBlowup
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q') (n : ℕ)

local notation "SourceRing" => pdTerm p k Q.n n
local notation "TargetRing" => pdTerm p k Q'.n n
local notation "SourceCopy" => ((Fin Q.n × Fin (n + 1)) →₀ k)
local notation "TargetCopy" => ((Fin Q'.n × Fin (n + 1)) →₀ k)
local notation "φ" => substituteCompleted p γ hk hr f n

private theorem inclusion_one (z : TargetRing ⊗[k] TargetCopy) :
    exteriorBaseChangeDegreeInclusion 1
      (TensorProduct.map LinearMap.id (exteriorPower.oneEquiv k TargetCopy).symm.toLinearMap z) =
      exteriorBaseChangeGenerator z := by
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    rw [TensorProduct.map_tmul]
    change a ⊗ₜ[k] ((exteriorPower.oneEquiv k TargetCopy).symm v).val =
      a ⊗ₜ[k] ExteriorAlgebra.ι k v
    simp [exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem exterior_on_generator (a : SourceRing) (v : SourceCopy) :
    substituteExterior p γ hk hr f n (a ⊗ₜ[k] ExteriorAlgebra.ι k v) =
      φ a • exteriorBaseChangeGenerator (completedJacobian p f n ((1 : TargetRing) ⊗ₜ[k] v)) := by
  unfold substituteExterior
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, exteriorOfBaseChange_tmul, exteriorOfBaseChangeAux_ι,
    map_smul, ExteriorAlgebra.map_apply_ι, exteriorToBaseChange_ι_all]

/-- 1 形式上の代入は完備化した Jacobian。 -/
theorem substituteForms_one (a : SourceRing) (v : SourceCopy) :
    substituteForms p γ hk hr f n 1
      (a ⊗ₜ[k] (exteriorPower.oneEquiv k SourceCopy).symm v) =
      TensorProduct.map LinearMap.id (exteriorPower.oneEquiv k TargetCopy).symm.toLinearMap
        (completedJacobian p f n (φ a ⊗ₜ[k] v)) := by
  apply exteriorBaseChangeDegreeInclusion_injective 1
  rw [map_inclusion, inclusion_one]
  change substituteExterior p γ hk hr f n
    (a ⊗ₜ[k] ((exteriorPower.oneEquiv k SourceCopy).symm v).val) = _
  have hv : ((exteriorPower.oneEquiv k SourceCopy).symm v).val = ExteriorAlgebra.ι k v := by
    simp [exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti]
  rw [hv, exterior_on_generator]
  rw [show φ a ⊗ₜ[k] v = φ a • ((1 : TargetRing) ⊗ₜ[k] v) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul]

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

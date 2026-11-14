module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionForms
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamWedge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionForms
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegree
import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegreeDifferential

/-!
# 多項式代入と完備分冪形式の外積

## 概要
完備分冪形式の代入が外積を保つことを示す。

## 方針
次数別の写像を総外積への代数射と照合し、同次部分の包含の単射性を使う。

## 規約
総外積には完備係数をテンソルする。

## 使われ方
BS 著者版 Theorem 6.4 の完備分冪 de Rham の cdga の射。
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

private def substituteExterior :
    SourceRing ⊗[k] ExteriorAlgebra k SourceCopy →ₐ[k] TargetRing ⊗[k] ExteriorAlgebra k TargetCopy :=
  (exteriorToBaseChange.comp ((ExteriorAlgebra.map (completedJacobian p f n)).comp
    exteriorOfBaseChange)).restrictScalars k |>.comp
      (Algebra.TensorProduct.map (substituteCompleted p γ hk hr f n) (AlgHom.id k _))

private theorem map_inclusion (i : ℕ) (x : SourceRing ⊗[k] (⋀[k]^i SourceCopy)) :
    exteriorBaseChangeDegreeInclusion i (substituteForms p γ hk hr f n i x) =
      substituteExterior p γ hk hr f n (exteriorBaseChangeDegreeInclusion i x) := by
  have h : exteriorBaseChangeDegreeInclusion (S := TargetRing) i
      (TensorProduct.map (substituteCompleted p γ hk hr f n).toLinearMap LinearMap.id x) =
      Algebra.TensorProduct.map (substituteCompleted p γ hk hr f n) (AlgHom.id k _)
        (exteriorBaseChangeDegreeInclusion i x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a z => rfl
    | add a z ha hz => simp only [map_add, ha, hz]
  unfold substituteForms substituteExterior
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  change exteriorBaseChangeDegreeInclusion i (exteriorDegreeToBaseChange i _) = _
  rw [exteriorDegreeToBaseChange_inclusion, exteriorPower.coe_map]
  rw [← h]
  rfl

omit [Fact p.Prime] in
private theorem inclusion_wedge (r i j : ℕ)
    (x : pdTerm p k r n ⊗[k] (⋀[k]^i ((Fin r × Fin (n + 1)) →₀ k)))
    (y : pdTerm p k r n ⊗[k] (⋀[k]^j ((Fin r × Fin (n + 1)) →₀ k))) :
    exteriorBaseChangeDegreeInclusion (i + j) (pdWedge p k r ⦋n⦌ i j x y) =
      exteriorBaseChangeDegreeInclusion i x * exteriorBaseChangeDegreeInclusion j y := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mul, ha, hb]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add b c hb hc => simp only [map_add, mul_add, hb, hc]
    | tmul b y =>
      simp only [pdWedge, wedgeTensor]
      change (a * b) ⊗ₜ[k] (x.val * y.val) = (a ⊗ₜ[k] x.val) * (b ⊗ₜ[k] y.val)
      rw [Algebra.TensorProduct.tmul_mul_tmul]

private theorem substituteForms_wedge_aux (i j : ℕ)
    (x : SourceRing ⊗[k] (⋀[k]^i SourceCopy)) (y : SourceRing ⊗[k] (⋀[k]^j SourceCopy)) :
    substituteForms p γ hk hr f n (i + j) (pdWedge p k Q.n ⦋n⦌ i j x y) =
      pdWedge p k Q'.n ⦋n⦌ i j (substituteForms p γ hk hr f n i x)
        (substituteForms p γ hk hr f n j y) := by
  apply exteriorBaseChangeDegreeInclusion_injective (i + j)
  rw [map_inclusion, inclusion_wedge, inclusion_wedge, map_inclusion, map_inclusion, map_mul]

/-- 余単体の各項で、完備分冪形式に多項式を代入する。 -/
def substituteRowForms (i : ℕ) :
    (pdRow p k Q.n i).obj ⦋n⦌ ⟶ (pdRow p k Q'.n i).obj ⦋n⦌ :=
  ModuleCat.ofHom (substituteForms p γ hk hr f n i)

/-- 完備分冪形式の多項式代入は外積と可換。 -/
theorem substituteForms_wedge (i j : ℕ)
    (x : (pdRow p k Q.n i).obj ⦋n⦌) (y : (pdRow p k Q.n j).obj ⦋n⦌) :
    substituteRowForms p γ hk hr f n (i + j) (pdWedge p k Q.n ⦋n⦌ i j x y) =
      pdWedge p k Q'.n ⦋n⦌ i j (substituteRowForms p γ hk hr f n i x)
        (substituteRowForms p γ hk hr f n j y) :=
  substituteForms_wedge_aux p γ hk hr f n i j x y

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFrameLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFrameLift
import all SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.CompletedPDEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve

/-!
# 指定した頂点変数の持ち上げによる分冪射

## 概要
各頂点の変数像を任意に指定し、それを延長する分冪射の存在と一意性を示す。

## 方針
多項式枠の核の条件を剰余で確認し、完備分冪包の普遍性を適用する。

## 規約
変数像は剰余構造射を持ち上げることだけを要求する。

## 使われ方
Berthelot III.4、Stacks 07HP。分冪 Čech の有限段の余積の普遍性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R] {κ : Cardinal.{u}}
variable (X : CrysOver p γ R κ) {S : Type u} (s : S → R) (hp : (p : k) ∈ J)
local notation "hJ" => crysResidue_kernel_of_tower (J := J) R
local notation "D" n => PDCechNerve.term p γ hp hJ s n
variable (n : ℕ) (v : S × Fin (n + 1) → X.B)
variable (hv : ∀ x, Ideal.Quotient.mk X.JB (v x) = X.sec (s x.1))

include hv in
/-- 指定した頂点変数像を延長する分冪射は一意に存在する。 -/
theorem existsUnique_pdCechVariableLift :
    ∃! f : (D n).carrier →ₐ[k] X.B,
      (D n).dividedPowers.IsDPMorphism X.δ f.toRingHom ∧
        ∀ x, f ((D n).unit (MvPolynomial.X x)) = v x := by
  let poly : pdFrame k S n →ₐ[k] X.B := MvPolynomial.aeval v
  have hpoly : (Ideal.Quotient.mkₐ k X.JB).comp poly =
      (crysResidueSectionAlgHom X).comp (pdFrameEval (k := k) s n) := by
    apply MvPolynomial.algHom_ext
    intro x
    change Ideal.Quotient.mk X.JB (MvPolynomial.aeval (R := k) v (MvPolynomial.X x)) =
      X.sec (pdFrameEval (k := k) s n (MvPolynomial.X x))
    rw [MvPolynomial.aeval_X, pdFrameEval_X]
    exact hv x
  have hker : (RingHom.ker (pdFrameEval (k := k) s n)).map poly.toRingHom ≤ X.JB := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change poly b ∈ X.JB
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := DFunLike.congr_fun hpoly b
    change Ideal.Quotient.mk X.JB (poly b) = X.sec (pdFrameEval (k := k) s n b) at h
    rw [RingHom.mem_ker.mp hb, map_zero] at h
    exact h
  obtain ⟨f, ⟨hf, hfu⟩, hu⟩ := (D n).isEnvelope.lift X.δ X.isAdicComplete poly hker X.base_dp
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · intro x
    have h := DFunLike.congr_fun hfu (MvPolynomial.X x)
    simpa only [poly, AlgHom.comp_apply, MvPolynomial.aeval_X] using h
  · intro g hg
    apply hu g
    refine ⟨hg.1, ?_⟩
    apply MvPolynomial.algHom_ext
    intro x
    change g ((D n).unit (MvPolynomial.X x)) = MvPolynomial.aeval (R := k) v (MvPolynomial.X x)
    rw [MvPolynomial.aeval_X]
    exact hg.2 x

end SerrePositivity.BhattScholze.Prismatic

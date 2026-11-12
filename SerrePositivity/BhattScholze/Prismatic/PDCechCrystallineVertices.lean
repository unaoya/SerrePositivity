module

public import SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCosimplicial
public import SerrePositivity.BhattScholze.Prismatic.CrystallineNilpotentComplete
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCosimplicial
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion
import all SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelope

/-!
# 結晶 Čech 有限冪商の頂点変数と射の判定

## 概要
有限冪商の変数像、剰余での値、頂点写像との両立を固定する。

## 方針
未商の変数像を標準商写像で送り、包の普遍性と商の全射性で射を判定する。

## 規約
台環の元として実際の変数像を記す。

## 使われ方
Berthelot III.4、Stacks 07HP。有限段の Čech 余積の普遍性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
variable {κ : Cardinal.{u}}
variable (hsmall : ∀ n, Cardinal.mk
  (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).carrier ≤ κ)

/-- 有限冪商の実際の頂点変数。 -/
@[expose] def pdCechQuotientVariable (e n : ℕ) (x : S × Fin (n + 1)) :
    (pdCechQuotient p γ hp R s hs hsmall e n).B :=
  Ideal.Quotient.mk _
    (PDCechNerve.variableImage p γ hp (crysResidue_kernel_of_tower (J := J) R) s n x)

/-- 頂点変数は、厚化の剰余で指定した剰余代数の元になる。 -/
theorem pdCechQuotientVariable_residue (e n : ℕ) (x : S × Fin (n + 1)) :
    Ideal.Quotient.mk (pdCechQuotient p γ hp R s hs hsmall e n).JB
      (pdCechQuotientVariable p γ hp R s hs hsmall e n x) =
        (pdCechQuotient p γ hp R s hs hsmall e n).sec (s x.1) := by
  let hJ := crysResidue_kernel_of_tower (J := J) R
  let D := PDCechNerve.term p γ hp hJ s n
  let E := crystallineCechResidueEquiv p γ hp hJ s hs n
  have h : Ideal.Quotient.mk D.ideal (PDCechNerve.variableImage p γ hp hJ s n x) =
      E.symm (s x.1) := by
    apply E.injective
    rw [crystallineCechResidueEquiv_mk, PDCechNerve.augmentation_variableImage]
    exact (E.apply_symm_apply (s x.1)).symm
  change crystallineQuotientResidueMap p e
    (Ideal.Quotient.mk D.ideal (PDCechNerve.variableImage p γ hp hJ s n x)) =
      crystallineQuotientResidueMap p e (E.symm (s x.1))
  exact congrArg (crystallineQuotientResidueMap p e) h

/-- 頂点写像は有限冪商の実際の変数を対応する変数に送る。 -/
@[simp] theorem pdCechQuotientVariable_map (e : ℕ) {m n : ℕ}
    (θ : Fin (m + 1) → Fin (n + 1)) (x : S × Fin (m + 1)) :
    (pdCechQuotientMap p γ hp R s hs hsmall e θ).toAlgHom
      (pdCechQuotientVariable p γ hp R s hs hsmall e m x) =
        pdCechQuotientVariable p γ hp R s hs hsmall e n (x.1, θ x.2) := by
  unfold pdCechQuotientVariable
  rw [pdCechQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _)
    (PDCechNerve.mapCopies_variableImage p γ hp
      (crysResidue_kernel_of_tower (J := J) R) s θ x)

/-- 有限冪商からの厚化の射は、頂点変数の像ですでに一意に決まる。 -/
theorem pdCechQuotient_hom_ext_variables (e n : ℕ) {X : CrysOver p γ R κ}
    {f g : pdCechQuotient p γ hp R s hs hsmall e n ⟶ X}
    (h : ∀ x : S × Fin (n + 1),
      f.toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e n x) =
      g.toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e n x)) : f = g := by
  let hJ := crysResidue_kernel_of_tower (J := J) R
  let D := PDCechNerve.term p γ hp hJ s n
  let q : D.carrier →ₐ[k] (pdCechQuotient p γ hp R s hs hsmall e n).B :=
    Ideal.Quotient.mkₐ k _
  have hq : D.dividedPowers.IsDPMorphism
      (pdCechQuotient p γ hp R s hs hsmall e n).δ q.toRingHom := by
    change D.dividedPowers.IsDPMorphism
      (PDAdicCompletion.quotientDividedPowers p D.dividedPowers
        (pdCechPrime_mem p γ hp R s n) e) _
    exact DividedPowers.Quotient.isDPMorphism _ _
  have hfg : f.toAlgHom.comp q = g.toAlgHom.comp q := by
    apply D.isEnvelope.hom_ext X.isAdicComplete (f.dp.comp _ hq) (g.dp.comp _ hq)
    apply MvPolynomial.algHom_ext
    intro x
    exact h x
  apply pdCechQuotientHom_ext p γ hp R s hs hsmall e n
  intro b
  exact DFunLike.congr_fun hfg b

end SerrePositivity.BhattScholze.Prismatic

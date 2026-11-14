module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFrameLiftResidue
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineVertices
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineVertices
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve

/-!
# 指定変数による有限冪商からの射の普遍性

## 概要
標的で指定した p 冪が消えるとき、剰余と両立する変数像は厚化の射へ一意に延びる。

## 方針
完備分冪包からの射を作り、剰余との可換性を確認して有限冪商へ降ろす。

## 規約
標的の消滅指数を型に残す。

## 使われ方
Berthelot III.4、Stacks 07HP。各有限段の Čech 余積の desc。
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

/-- 指定した変数像を持つ有限冪商からの厚化の射は一意に存在する。 -/
theorem existsUnique_pdCechQuotientVariablesLift (e n : ℕ) (X : CrysOver p γ R κ)
    (v : S × Fin (n + 1) → X.B)
    (hv : ∀ x, Ideal.Quotient.mk X.JB (v x) = X.sec (s x.1))
    (hkill : (p : X.B) ^ (e + 2) = 0) :
    ∃! f : pdCechQuotient p γ hp R s hs hsmall e n ⟶ X,
      ∀ x, f.toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e n x) = v x := by
  let hJ := crysResidue_kernel_of_tower (J := J) R
  let D := PDCechNerve.term p γ hp hJ s n
  obtain ⟨f, ⟨hf, hfv⟩, _⟩ := existsUnique_pdCechVariableLift X s hp n v hv
  have hres := pdCechHom_residue_of_variables p γ hp hJ s X n f hf
    (fun x => (congrArg (Ideal.Quotient.mk X.JB) (hfv x)).trans (hv x))
  have hc := pdCechHom_comp_residueSection p γ hp hJ s X n hs f hf hres
  let q := crystallinePDQuotientLift p γ R D.dividedPowers
    (pdCechPrime_mem p γ hp R s n) D.isEnvelope.base_dp
    (pdCechResidueSection p γ hp R s hs n)
    (pdCechResidueSection_base p γ hp R s hs n) (hsmall n) X e f hf hkill hc
  have hq : ∀ x, q.toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e n x) = v x := by
    intro x
    dsimp only [q, crystallinePDQuotientLift, crystallinePDQuotientLiftAlg,
      pdCechQuotientVariable, PDCechNerve.variableImage]
    exact hfv x
  refine ⟨q, hq, ?_⟩
  intro g hg
  apply pdCechQuotient_hom_ext_variables p γ hp R s hs hsmall e n
  intro x
  exact (hg x).trans (hq x).symm

end SerrePositivity.BhattScholze.Prismatic

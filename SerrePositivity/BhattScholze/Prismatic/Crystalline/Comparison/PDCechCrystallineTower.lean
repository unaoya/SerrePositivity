module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineCoproduct
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechProWeakTerminal
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientTower
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Currying
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineCosimplicial
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineCoproduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechProWeakTerminal
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientTower
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 結晶分冪 Čech の塔と各段の有限冪

## 概要
有限 p 冪商の遷移を余単体的な射にし、各段の Čech データと両立させる。

## 方針
代表元上で単体射との可換性を示す。反対圏で同じ正方形を射影との両立として読む。

## 規約
環の向きの二重添字は ℕᵒᵖ × Δ、サイトの零次の塔は ℕ。

## 使われ方
BS 著者版 Theorem 5.2、Berthelot III.4、Stacks 07HP。通常の圏論の pro Čech データ。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
variable {κ : Cardinal.{u}}
variable (hsmall : ∀ n, Cardinal.mk
  (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).carrier ≤ κ)

/-- 隣り合う有限 p 冪商の遷移は、余単体的な厚化の射となる。 -/
def pdCechQuotientTransition (e : ℕ) :
    pdCechQuotientCosimplicial p γ hp R s hs hsmall (e + 1) ⟶
      pdCechQuotientCosimplicial p γ hp R s hs hsmall e where
  app n := (crystallinePDQuotientTransition p γ R
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n.len).dividedPowers
      (pdCechPrime_mem p γ hp R s n.len)
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n.len).isEnvelope.base_dp
      (pdCechResidueSection p γ hp R s hs n.len)
      (pdCechResidueSection_base p γ hp R s hs n.len) (hsmall n.len)
      e (e + 1) (Nat.le_succ e))
  naturality m n θ := by
    apply pdCechQuotientHom_ext p γ hp R s hs hsmall (e + 1) m.len
    intro x
    change (crystallinePDQuotientTransition p γ R
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n.len).dividedPowers
      (pdCechPrime_mem p γ hp R s n.len)
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n.len).isEnvelope.base_dp
      (pdCechResidueSection p γ hp R s hs n.len)
      (pdCechResidueSection_base p γ hp R s hs n.len) (hsmall n.len)
      e (e + 1) (Nat.le_succ e)).toAlgHom
      ((pdCechQuotientMap p γ hp R s hs hsmall (e + 1) θ.toOrderHom).toAlgHom
        (Ideal.Quotient.mk _ x)) =
      (pdCechQuotientMap p γ hp R s hs hsmall e θ.toOrderHom).toAlgHom
        ((crystallinePDQuotientTransition p γ R
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s m.len).dividedPowers
      (pdCechPrime_mem p γ hp R s m.len)
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s m.len).isEnvelope.base_dp
      (pdCechResidueSection p γ hp R s hs m.len)
      (pdCechResidueSection_base p γ hp R s hs m.len) (hsmall m.len)
      e (e + 1) (Nat.le_succ e)).toAlgHom (Ideal.Quotient.mk _ x))
    rw [pdCechQuotientMap_mk, crystallinePDQuotientTransition_mk,
      crystallinePDQuotientTransition_mk, pdCechQuotientMap_mk]

/-- 環の向きの二重添字による分冪 Čech の塔。 -/
def pdCechTower : ℕᵒᵖ × SimplexCategory ⥤ CrysOver p γ R κ :=
  Functor.uncurry.obj (Functor.ofOpSequence (pdCechQuotientTransition p γ hp R s hs hsmall))

/-- 各有限段の Čech 脈体と、その射影を保つ塔の遷移。 -/
def pdCechTowerProCechData :
    ProCechNerveData (pdCechTowerZero p γ hp R s hs (hsmall 0)) where
  level e := pdCechQuotientCechData p γ hp R s hs hsmall e
  transition e := NatTrans.op (pdCechQuotientTransition p γ hp R s hs hsmall e)
  transition_proj e n i := by
    apply Quiver.Hom.unop_inj
    exact (pdCechQuotientTransition p γ hp R s hs hsmall e).naturality
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)

/-- 零次の塔の pro 弱終性。各段の Čech データと同じ塔を使う。 -/
theorem pdCechTower_proWeaklyTerminal :
    IsProWeaklyTerminal (pdCechTowerZero p γ hp R s hs (hsmall 0)) :=
  pdCechTowerZero_proWeaklyTerminal p γ hp R s hs (hsmall 0)

end SerrePositivity.BhattScholze.Prismatic

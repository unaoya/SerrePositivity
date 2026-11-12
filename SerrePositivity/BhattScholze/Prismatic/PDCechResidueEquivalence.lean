module

public import SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelope

/-!
# 全射な枠の分冪 Čech 包の剰余

## 概要
剰余代数を覆う枠では、分冪包をその分冪イデアルで割ると剰余代数に戻る。

## 方針
零次の全射性を一つの頂点への変数の移送で全次数へ延ばし、分冪包の剰余同型を使う。

## 規約
基底の分冪と p の像の条件を明示する。有限 p 冪商を取る前の剰余の同定。

## 使われ方
Berthelot III.4、Stacks 07HP。分冪 Čech の塔の各項の結晶厚化の構造射。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (p : ℕ) {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hJ : J ≤ RingHom.ker (algebraMap k A))
variable {S : Type u} (s : S → A) (hs : Function.Surjective (pdFrameEval (k := k) s 0))

include hs in
/-- 枠の零次の全射性はすべての次数の評価の全射性を与える。 -/
theorem pdFrameEval_surjective (n : ℕ) : Function.Surjective (pdFrameEval (k := k) s n) := by
  intro a
  obtain ⟨f, hf⟩ := hs a
  refine ⟨MvPolynomial.rename (fun x : S × Fin 1 => (x.1, (0 : Fin (n + 1)))) f, ?_⟩
  change MvPolynomial.aeval (fun x : S × Fin (n + 1) => s x.1) _ = a
  rw [MvPolynomial.aeval_rename]
  exact hf

/-- 全射な枠の分冪包の剰余と元の剰余代数の標準同型。 -/
def crystallineCechResidueEquiv (n : ℕ) :
    ((PDCechNerve.term p γ hp hJ s n).carrier ⧸
      (PDCechNerve.term p γ hp hJ s n).ideal) ≃ₐ[k] A :=
  ((PDCechNerve.term p γ hp hJ s n).isEnvelope.quotientEquiv hp
    (PDCechNerve.base_le_ker hJ s n)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (pdFrameEval_surjective s hs n))

/-- 剰余同型は包の標準脚を元の枠の評価に送る。 -/
@[simp] theorem crystallineCechResidueEquiv_mk_unit (n : ℕ) (f : pdFrame k S n) :
    crystallineCechResidueEquiv p γ hp hJ s hs n
      (Ideal.Quotient.mk _ ((PDCechNerve.term p γ hp hJ s n).unit f)) =
      pdFrameEval (k := k) s n f := by
  unfold crystallineCechResidueEquiv
  rw [AlgEquiv.trans_apply, IsCompletedPDEnvelope.quotientEquiv_mk_unit,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- 分冪包の剰余同型からの評価は、既存の増強そのもの。 -/
theorem crystallineCechResidueEquiv_mk (n : ℕ)
    (b : (PDCechNerve.term p γ hp hJ s n).carrier) :
    crystallineCechResidueEquiv p γ hp hJ s hs n (Ideal.Quotient.mk _ b) =
      PDCechNerve.augmentation p γ hp hJ s n b := by
  let D := PDCechNerve.term p γ hp hJ s n
  let E := crystallineCechResidueEquiv p γ hp hJ s hs n
  let f := E.toAlgHom.comp (Ideal.Quotient.mkₐ k D.ideal)
  have h : f = PDCechNerve.augmentation p γ hp hJ s n := by
    apply D.isEnvelope.hom_ext (PDCechNerve.complete_target p hp hJ)
      (isDPMorphismToBot D.dividedPowers f.toRingHom (fun x hx => by
        change E (Ideal.Quotient.mk D.ideal x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]))
      (PDCechNerve.augmentation_isDPMorphism p γ hp hJ s n)
    apply AlgHom.ext
    intro x
    exact (crystallineCechResidueEquiv_mk_unit p γ hp hJ s hs n x).trans
      (PDCechNerve.augmentation_unit p γ hp hJ s n x).symm
  exact DFunLike.congr_fun h b

end SerrePositivity.BhattScholze.Prismatic

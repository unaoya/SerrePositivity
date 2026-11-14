module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFrameVariablesLift
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechResidueEquivalence
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.CompletedPDEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFrameLift

/-!
# 指定した分冪射の剰余構造射との照合

## 概要
頂点変数の剰余を保つ分冪射は、包の増強と剰余構造射の正方形を保つ。

## 方針
分冪包の普遍性で二つの剰余評価を変数上で比較する。

## 規約
変数像の選び方には依存しない。零次に限定せず全次数で述べる。

## 使われ方
Berthelot III.4、Stacks 07HP。各有限段の Čech 余積の desc の剰余条件。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) {R : Type u} [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
variable (hJ : J ≤ RingHom.ker (algebraMap k R)) {S : Type u} (s : S → R)
variable {κ : Cardinal.{u}} (X : CrysOver p γ R κ) (n : ℕ)

/-- 頂点変数の剰余の一致から、増強との正方形の可換性が従う。 -/
theorem pdCechHom_residue_of_variables
    (f : (PDCechNerve.term p γ hp hJ s n).carrier →ₐ[k] X.B)
    (hf : (PDCechNerve.term p γ hp hJ s n).dividedPowers.IsDPMorphism X.δ f.toRingHom)
    (hgen : ∀ x, Ideal.Quotient.mk X.JB
      (f ((PDCechNerve.term p γ hp hJ s n).unit (MvPolynomial.X x))) = X.sec (s x.1)) :
    (Ideal.Quotient.mk X.JB).comp f.toRingHom =
      X.sec.comp (PDCechNerve.augmentation p γ hp hJ s n).toRingHom := by
  let D := PDCechNerve.term p γ hp hJ s n
  let a := (Ideal.Quotient.mkₐ k X.JB).comp f
  let b := (crysResidueSectionAlgHom X).comp (PDCechNerve.augmentation p γ hp hJ s n)
  have ht : IsAdicComplete (Ideal.span {(p : X.B ⧸ X.JB)}) (X.B ⧸ X.JB) := by
    apply isAdicComplete_of_natCast_zero
    change Ideal.Quotient.mk X.JB (p : X.B) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (X.prime_mem hp)
  have hab : a = b := by
    apply D.isEnvelope.hom_ext ht
      (isDPMorphismToBot D.dividedPowers a.toRingHom (fun x hx => by
        change Ideal.Quotient.mk X.JB (f x) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf.ideal_comp (Ideal.mem_map_of_mem _ hx))))
      (isDPMorphismToBot D.dividedPowers b.toRingHom (fun x hx => by
        change X.sec (PDCechNerve.augmentation p γ hp hJ s n x) = 0
        have hz : PDCechNerve.augmentation p γ hp hJ s n x = 0 :=
          RingHom.mem_ker.mp ((PDCechNerve.augmentation_ker p γ hp hJ s n).symm ▸ hx)
        rw [hz, map_zero]))
    apply MvPolynomial.algHom_ext
    intro x
    change Ideal.Quotient.mk X.JB (f (D.unit (MvPolynomial.X x))) =
      X.sec (PDCechNerve.augmentation p γ hp hJ s n (D.unit (MvPolynomial.X x)))
    rw [PDCechNerve.augmentation_unit, pdFrameEval_X]
    exact hgen x
  exact congrArg AlgHom.toRingHom hab

omit [IsScalarTower k (k ⧸ J) R] in
/-- 増強との可換性から、包の剰余同型の逆との可換性が従う。 -/
theorem pdCechHom_comp_residueSection
    (hs : Function.Surjective (pdFrameEval (k := k) s 0))
    (f : (PDCechNerve.term p γ hp hJ s n).carrier →ₐ[k] X.B)
    (hf : (PDCechNerve.term p γ hp hJ s n).dividedPowers.IsDPMorphism X.δ f.toRingHom)
    (hres : (Ideal.Quotient.mk X.JB).comp f.toRingHom =
      X.sec.comp (PDCechNerve.augmentation p γ hp hJ s n).toRingHom) :
    (Ideal.quotientMap X.JB f.toRingHom
      (Ideal.map_le_iff_le_comap.mp hf.ideal_comp)).comp
        (crystallineCechResidueEquiv p γ hp hJ s hs n).symm.toRingHom = X.sec := by
  ext r
  let E := crystallineCechResidueEquiv p γ hp hJ s hs n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (E.symm r)
  have he : PDCechNerve.augmentation p γ hp hJ s n b = r := by
    rw [← crystallineCechResidueEquiv_mk p γ hp hJ s hs n b, hb]
    exact E.apply_symm_apply r
  change (Ideal.quotientMap X.JB f.toRingHom
    (Ideal.map_le_iff_le_comap.mp hf.ideal_comp)) (E.symm r) = X.sec r
  rw [← hb, Ideal.quotientMap_mk]
  have h := DFunLike.congr_fun hres b
  change Ideal.Quotient.mk X.JB (f b) = X.sec (PDCechNerve.augmentation p γ hp hJ s n b) at h
  exact h.trans (congrArg X.sec he)

end SerrePositivity.BhattScholze.Prismatic

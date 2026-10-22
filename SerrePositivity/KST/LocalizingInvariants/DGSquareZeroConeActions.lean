module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeOperator
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftElements
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation

/-!
概要：包含の次数一 shift が、元の左右作用と満たす符号付き Leibniz の二式。
方針：tensor–shift の斉次式から、元の双加群射の作用保存へ戻す。
規約：左作用の次数符号を保持する。使われ方：cone の追加微分の derivation 則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroCone
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)
  (f : M ⟶ Bimod.regular A)

lemma shiftedInclusion_actLeft (p q : ℤ) (a : A.X.X p) (m : M.X.X (q + 1)) :
    (shiftedInclusion A M f.hom).val.v (p + q) (p + q + 1) rfl
      ((DGBimoduleShift.obj M 1).actLeft.f (p + q)
        (ιTensorObj A.X (M.X⟦(1 : ℤ)⟧) p q (p + q) rfl (a ⊗ₜ[R] m))) =
    p.negOnePow • μ[A.X].f (p + q + 1)
      (ιTensorObj A.X A.X p (q + 1) (p + q + 1) (by omega)
        (a ⊗ₜ[R] f.hom.f (q + 1) m)) := by
  rw [shiftedInclusion_v]
  change f.hom.f (p + q + 1)
    (((cochainTensorShiftRight A.X M.X 1).hom ≫ M.actLeft⟦(1 : ℤ)⟧').f (p + q)
      (ιTensorObj A.X (M.X⟦(1 : ℤ)⟧) p q (p + q) rfl (a ⊗ₜ[R] m))) = _
  rw [chain_comp_apply, tensorShiftRight_apply]
  simp only [mul_one]
  rw [chain_units_smul, chain_units_smul]
  congr 1
  have h := congrArg (fun k => k.f (p + q + 1)
    (ιTensorObj A.X M.X p (q + 1) (p + q + 1) (by omega) (a ⊗ₜ[R] m))) f.left_act_hom
  change f.hom.f (p + q + 1)
    (M.actLeft.f (p + q + 1)
      (ιTensorObj A.X M.X p (q + 1) (p + q + 1) (by omega) (a ⊗ₜ[R] m))) =
    μ[A.X].f (p + q + 1) ((A.X ◁ f.hom).f (p + q + 1)
      (ιTensorObj A.X M.X p (q + 1) (p + q + 1) (by omega) (a ⊗ₜ[R] m))) at h
  exact h.trans (congrArg (fun z => μ[A.X].f (p + q + 1) z)
    (whiskerLeft_apply A.X f.hom p (q + 1) (p + q + 1) (by omega) a m))

lemma shiftedInclusion_actRight (p q : ℤ) (m : M.X.X (p + 1)) (a : A.X.X q) :
    (shiftedInclusion A M f.hom).val.v (p + q) (p + q + 1) rfl
      ((DGBimoduleShift.obj M 1).actRight.f (p + q)
        (ιTensorObj (M.X⟦(1 : ℤ)⟧) A.X p q (p + q) rfl (m ⊗ₜ[R] a))) =
    μ[A.X].f (p + q + 1)
      (ιTensorObj A.X A.X (p + 1) q (p + q + 1) (by omega)
        (f.hom.f (p + 1) m ⊗ₜ[R] a)) := by
  rw [shiftedInclusion_v]
  change f.hom.f (p + q + 1)
    (((cochainTensorShiftLeft M.X A.X 1).hom ≫ M.actRight⟦(1 : ℤ)⟧').f (p + q)
      (ιTensorObj (M.X⟦(1 : ℤ)⟧) A.X p q (p + q) rfl (m ⊗ₜ[R] a))) = _
  rw [chain_comp_apply, tensorShiftLeft_apply]
  have h := congrArg (fun k => k.f (p + q + 1)
    (ιTensorObj M.X A.X (p + 1) q (p + q + 1) (by omega) (m ⊗ₜ[R] a))) f.right_act_hom
  change f.hom.f (p + q + 1)
    (M.actRight.f (p + q + 1)
      (ιTensorObj M.X A.X (p + 1) q (p + q + 1) (by omega) (m ⊗ₜ[R] a))) =
    μ[A.X].f (p + q + 1) ((f.hom ▷ A.X).f (p + q + 1)
      (ιTensorObj M.X A.X (p + 1) q (p + q + 1) (by omega) (m ⊗ₜ[R] a))) at h
  exact h.trans (congrArg (fun z => μ[A.X].f (p + q + 1) z)
    (whiskerRight_apply f.hom A.X (p + 1) q (p + q + 1) (by omega) m a))

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

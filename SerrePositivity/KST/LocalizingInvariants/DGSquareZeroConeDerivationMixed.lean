module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeDerivationTests
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeActions
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProductElements

/-!
概要：cone の追加微分の Leibniz 差を、底同士と二つの混合成分で消す。
方針：平方零積の四成分と、shift した包含の左右作用保存を用いる。
規約：左次数の符号を保持。使われ方：負次数層の cone に実 dg 代数構造を入れる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroCone
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)
  (f : M ⟶ Bimod.regular A)

lemma defect_ll (p q : ℤ) (a : A.X.X p) (b : A.X.X q) :
    defect A M f.hom p q ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f p a)
      ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f q b) = 0 := by
  dsimp only [defect, AlgebraPerturbation.defect]
  rw [SquareZero.mul_ll_apply, operator_inl_apply, operator_inl_apply, operator_inl_apply]
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, smul_zero,
    zero_add, sub_self]

lemma defect_lr (p q : ℤ) (a : A.X.X p) (m : M.X.X (q + 1)) :
    defect A M f.hom p q ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f p a)
      ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f q m) = 0 := by
  dsimp only [defect, AlgebraPerturbation.defect]
  rw [SquareZero.mul_lr_apply, operator_inr_apply, operator_inl_apply, operator_inr_apply]
  simp only [TensorProduct.zero_tmul, map_zero, zero_add]
  rw [SquareZero.mul_ll_apply]
  apply sub_eq_zero.mpr
  have h := shiftedInclusion_actLeft A M f p q a m
  rw [shiftedInclusion_v] at h
  exact (congrArg (fun z => (biprod.inl : A.X ⟶ (splitAlgebra A M).X).f (p + q + 1) z)
    h).trans (chain_units_smul biprod.inl (p + q + 1) p.negOnePow _)

lemma defect_rl (p q : ℤ) (m : M.X.X (p + 1)) (a : A.X.X q) :
    defect A M f.hom p q ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m)
      ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f q a) = 0 := by
  dsimp only [defect, AlgebraPerturbation.defect]
  rw [SquareZero.mul_rl_apply, operator_inr_apply, operator_inr_apply, operator_inl_apply]
  simp only [TensorProduct.tmul_zero, map_zero, smul_zero, add_zero]
  rw [SquareZero.mul_ll_apply]
  apply sub_eq_zero.mpr
  have h := shiftedInclusion_actRight A M f p q m a
  rw [shiftedInclusion_v] at h
  exact congrArg (fun z => (biprod.inl : A.X ⟶ (splitAlgebra A M).X).f (p + q + 1) z) h

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeDerivationMixed
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbation

/-!
概要：単一の負次数にある層の包含は、平方零代数上の実次数一 derivation を与える。
方針：混合三成分は包含の作用保存、残る成分は次数の分離から零にする。
規約：Leibniz 則を仮定入力にしない。使われ方：Postnikov cone の実 dg 代数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroCone
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)
  (f : M ⟶ Bimod.regular A) (k : ℤ) (hk : k < 0)
  [hLower : M.X.IsStrictlyGE k] [hUpper : M.X.IsStrictlyLE k]

include k hk hLower hUpper

lemma defect_rr (p q : ℤ) (m : M.X.X (p + 1)) (m' : M.X.X (q + 1)) :
    defect A M f.hom p q ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m)
      ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f q m') = 0 := by
  let i : M.X ⟶ A.X := f.hom
  change defect A M i p q
    ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m)
    ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f q m') = 0
  have vanish (r : ℤ) (hr : r ≠ k) (x : M.X.X r) : x = 0 := by
    have hz : IsZero (M.X.X r) := by
      by_cases h : r < k
      · exact M.X.isZero_of_isStrictlyGE k r h
      · exact M.X.isZero_of_isStrictlyLE k r (by omega)
    have : Subsingleton (M.X.X r) := ModuleCat.isZero_iff_subsingleton.1 hz
    exact Subsingleton.elim _ _
  by_cases hp : p + 1 = k
  · by_cases hq : q + 1 = k
    · have hz : IsZero ((DGBimoduleShift.obj M 1).X.X (p + q + 1)) := by
        change IsZero (M.X.X ((p + q + 1) + 1))
        exact M.X.isZero_of_isStrictlyGE k _ (by omega)
      have : Subsingleton ((DGBimoduleShift.obj M 1).X.X (p + q + 1)) :=
        ModuleCat.isZero_iff_subsingleton.1 hz
      dsimp only [defect, AlgebraPerturbation.defect]
      rw [SquareZero.mul_rr_apply, map_zero, operator_inr_apply, operator_inr_apply,
        SquareZero.mul_lr_apply, SquareZero.mul_rl_apply]
      have he (x : (DGBimoduleShift.obj M 1).X.X (p + q + 1)) : x = 0 :=
        Subsingleton.elim _ _
      have hl := he ((DGBimoduleShift.obj M 1).actLeft.f (p + q + 1)
        (ιTensorObj A.X (DGBimoduleShift.obj M 1).X (p + 1) q (p + q + 1)
          (by omega) (i.f (p + 1) m ⊗ₜ[R] m')))
      have hr := he ((DGBimoduleShift.obj M 1).actRight.f (p + q + 1)
        (ιTensorObj (DGBimoduleShift.obj M 1).X A.X p (q + 1) (p + q + 1)
          (by omega) (m ⊗ₜ[R] i.f (q + 1) m')))
      apply sub_eq_zero.mpr
      let j := (biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f
        (p + q + 1)
      exact ((congrArg₂ (· + ·) (congrArg (fun x => j x) hl)
        (congrArg (fun x => p.negOnePow • j x) hr)).trans
          (by simp only [map_zero, smul_zero, zero_add])).symm
    · have hm := vanish (q + 1) hq m'
      subst m'
      simp only [defect, AlgebraPerturbation.defect, map_zero, TensorProduct.tmul_zero,
        smul_zero, zero_add, sub_self]
  · have hm := vanish (p + 1) hp m
    subst m
    simp only [defect, AlgebraPerturbation.defect, map_zero, TensorProduct.zero_tmul,
      smul_zero, zero_add, sub_self]

lemma operator_isDerivation :
    AlgebraPerturbation.IsDerivation (splitAlgebra A M) (operator A M f.hom) :=
  operator_isDerivation_of_four A M f.hom (defect_ll A M f) (defect_lr A M f)
    (defect_rl A M f) (defect_rr A M f k hk)

def algebra : Mon (Complex R) :=
  AlgebraPerturbation.algebra (splitAlgebra A M) (operator A M f.hom)
    (operator_closed A M f.hom) (operator_square_zero A M f.hom)
    (operator_isDerivation A M f k hk) (operator_unit A M f.hom)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProjection
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
概要：層包含の shift から、分裂平方零代数上の追加微分の作用素を作る。
方針：shift 係数から元の代数への閉 cochain を、直和の射影と包含で挟む。
規約：Leibniz 則は後で検証する。使われ方：Postnikov cone の微分変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroCone
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)
  (i : M.X ⟶ A.X)

abbrev splitAlgebra : Mon (Complex R) := SquareZero.algebra A (DGBimoduleShift.obj M 1)

def shiftedInclusion : Cocycle ((DGBimoduleShift.obj M 1).X) A.X 1 :=
  -(Cocycle.ofHom i).leftShift 1 1 (zero_add 1)

lemma shiftedInclusion_v (p : ℤ) :
    (shiftedInclusion A M i).val.v p (p + 1) rfl = i.f (p + 1) := by
  simp [shiftedInclusion, Cocycle.leftShift, Cochain.leftShift, Cochain.ofHom_v,
    CochainComplex.shiftFunctorObjXIso]

def operator : Cochain (splitAlgebra A M).X (splitAlgebra A M).X 1 :=
  ((Cochain.ofHom (biprod.snd : A.X ⊞ (DGBimoduleShift.obj M 1).X ⟶ _)).comp
    (shiftedInclusion A M i).val (zero_add 1)).comp (Cochain.ofHom biprod.inl) (add_zero 1)

lemma operator_closed : δ 1 2 (operator A M i) = 0 := by
  rw [operator, δ_comp_ofHom, δ_ofHom_comp, Cocycle.δ_eq_zero]
  simp

lemma operator_inl :
    (Cochain.ofHom (biprod.inl : A.X ⟶ (splitAlgebra A M).X)).comp
      (operator A M i) (zero_add 1) = 0 := by
  rw [operator, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, biprod.inl_snd]
  simp

lemma operator_square_zero :
    (operator A M i).comp (operator A M i) (rfl : (1 : ℤ) + 1 = 2) = 0 := by
  change (((Cochain.ofHom biprod.snd).comp (shiftedInclusion A M i).val
    (zero_add 1)).comp (Cochain.ofHom biprod.inl) (add_zero 1)).comp (operator A M i) _ = 0
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, operator_inl, Cochain.comp_zero]

lemma operator_unit : (Cochain.ofHom η[(splitAlgebra A M).X]).comp
    (operator A M i) (zero_add 1) = 0 := by
  change (Cochain.ofHom (η[A.X] ≫ biprod.inl)).comp (operator A M i) _ = 0
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, operator_inl]
  exact Cochain.comp_zero _ _

lemma operator_v (p : ℤ) : (operator A M i).v p (p + 1) rfl =
    (biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f p ≫
      i.f (p + 1) ≫ (biprod.inl : A.X ⟶ (splitAlgebra A M).X).f (p + 1) := by
  rw [operator, Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftedInclusion_v, Category.assoc]

lemma operator_inl_apply (p : ℤ) (a : A.X.X p) :
    (operator A M i).v p (p + 1) rfl
      ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f p a) = 0 := by
  have h := Cochain.congr_v (operator_inl A M i) p (p + 1) rfl
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at h
  exact ConcreteCategory.congr_hom h a

lemma operator_inr_apply (p : ℤ) (m : M.X.X (p + 1)) :
    (operator A M i).v p (p + 1) rfl
      ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m) =
        (biprod.inl : A.X ⟶ (splitAlgebra A M).X).f (p + 1) (i.f (p + 1) m) := by
  rw [operator_v]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun k => k.f p) (biprod.inr_snd (X := A.X) (Y := (DGBimoduleShift.obj M 1).X))) m
  change (biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f p
    ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m) = m at h
  change (biprod.inl : A.X ⟶ (splitAlgebra A M).X).f (p + 1) (i.f (p + 1)
    ((biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f p
      ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m))) = _
  rw [h]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

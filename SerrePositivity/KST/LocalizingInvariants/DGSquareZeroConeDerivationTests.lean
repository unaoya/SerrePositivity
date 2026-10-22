module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbationDefect
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeOperator

/-!
概要：cone の追加微分の Leibniz 則を、直和の四つの成分で判定する。
方針：直和の元の実分解と Leibniz 差の双加法性を使う。
規約：全ての斉次元での等式。使われ方：負次数の Postnikov 層の derivation 則。
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
  (i : M.X ⟶ A.X)

lemma element_decompose (p : ℤ) (a : (splitAlgebra A M).X.X p) :
    a = (biprod.inl : A.X ⟶ (splitAlgebra A M).X).f p
      ((biprod.fst : (splitAlgebra A M).X ⟶ A.X).f p a) +
      (biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p
        ((biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f p a) := by
  have h := congrArg (fun k => k.f p a)
    (biprod.total (X := A.X) (Y := (DGBimoduleShift.obj M 1).X))
  exact h.symm

abbrev defect := AlgebraPerturbation.defect (splitAlgebra A M) (operator A M i)

lemma operator_isDerivation_of_four
    (hll : ∀ p q (a : A.X.X p) (b : A.X.X q),
      defect A M i p q ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f p a)
        ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f q b) = 0)
    (hlr : ∀ p q (a : A.X.X p) (m : M.X.X (q + 1)),
      defect A M i p q ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f p a)
        ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f q m) = 0)
    (hrl : ∀ p q (m : M.X.X (p + 1)) (a : A.X.X q),
      defect A M i p q ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m)
        ((biprod.inl : A.X ⟶ (splitAlgebra A M).X).f q a) = 0)
    (hrr : ∀ p q (m : M.X.X (p + 1)) (m' : M.X.X (q + 1)),
      defect A M i p q ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p m)
        ((biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f q m') = 0) :
    AlgebraPerturbation.IsDerivation (splitAlgebra A M) (operator A M i) := by
  apply (AlgebraPerturbation.isDerivation_iff_defect _ _).2
  intro p q a b
  rw [element_decompose A M p a, element_decompose A M q b,
    AlgebraPerturbation.defect_add_left, AlgebraPerturbation.defect_add_right,
    AlgebraPerturbation.defect_add_right]
  have h₁ := hll p q ((biprod.fst : (splitAlgebra A M).X ⟶ A.X).f p a)
    ((biprod.fst : (splitAlgebra A M).X ⟶ A.X).f q b)
  have h₂ := hlr p q ((biprod.fst : (splitAlgebra A M).X ⟶ A.X).f p a)
    ((biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f q b)
  have h₃ := hrl p q
    ((biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f p a)
    ((biprod.fst : (splitAlgebra A M).X ⟶ A.X).f q b)
  have h₄ := hrr p q
    ((biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f p a)
    ((biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f q b)
  exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) h₁ h₂)
    (congrArg₂ (· + ·) h₃ h₄)).trans (by simp)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

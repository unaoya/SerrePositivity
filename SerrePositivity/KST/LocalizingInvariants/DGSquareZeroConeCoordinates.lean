module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeOperator
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
概要：層包含による微分変更の二座標と、その微分の行列式を供給する。
方針：元の直和の射影と包含を評価し、追加作用素の正符号の包含成分を保持する。
規約：底座標は鎖写像ではない。使われ方：元の mapping cone との実複体同型。
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

abbrev complex : Complex R := perturbComplex (splitAlgebra A M).X (operator A M i)
  (operator_closed A M i) (operator_square_zero A M i)

def baseF (p : ℤ) : (complex A M i).X p ⟶ A.X.X p :=
  (biprod.fst : (splitAlgebra A M).X ⟶ A.X).f p

def coefficientF (p : ℤ) : (complex A M i).X p ⟶ M.X.X (p + 1) :=
  (biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).f p

def baseInclusionF (p : ℤ) : A.X.X p ⟶ (complex A M i).X p :=
  (biprod.inl : A.X ⟶ (splitAlgebra A M).X).f p

def coefficientInclusionF (p : ℤ) : M.X.X (p + 1) ⟶ (complex A M i).X p :=
  (biprod.inr : (DGBimoduleShift.obj M 1).X ⟶ (splitAlgebra A M).X).f p

@[reassoc] lemma baseInclusionF_baseF (p : ℤ) :
    baseInclusionF A M i p ≫ baseF A M i p = 𝟙 _ :=
  congrArg (fun f => f.f p) (biprod.inl_fst (X := A.X) (Y := (DGBimoduleShift.obj M 1).X))

@[reassoc] lemma baseInclusionF_coefficientF (p : ℤ) :
    baseInclusionF A M i p ≫ coefficientF A M i p = 0 :=
  congrArg (fun f => f.f p) (biprod.inl_snd (X := A.X) (Y := (DGBimoduleShift.obj M 1).X))

@[reassoc] lemma coefficientInclusionF_baseF (p : ℤ) :
    coefficientInclusionF A M i p ≫ baseF A M i p = 0 :=
  congrArg (fun f => f.f p) (biprod.inr_fst (X := A.X) (Y := (DGBimoduleShift.obj M 1).X))

@[reassoc] lemma coefficientInclusionF_coefficientF (p : ℤ) :
    coefficientInclusionF A M i p ≫ coefficientF A M i p = 𝟙 _ :=
  congrArg (fun f => f.f p) (biprod.inr_snd (X := A.X) (Y := (DGBimoduleShift.obj M 1).X))

lemma coordinates_total (p : ℤ) :
    baseF A M i p ≫ baseInclusionF A M i p +
      coefficientF A M i p ≫ coefficientInclusionF A M i p = 𝟙 _ :=
  congrArg (fun f => f.f p) (biprod.total (X := A.X) (Y := (DGBimoduleShift.obj M 1).X))

lemma operator_baseF (p : ℤ) :
    (operator A M i).v p (p + 1) rfl ≫ baseF A M i (p + 1) =
      coefficientF A M i p ≫ i.f (p + 1) := by
  have hv : (operator A M i).v p (p + 1) rfl =
      coefficientF A M i p ≫ i.f (p + 1) ≫ baseInclusionF A M i (p + 1) := operator_v A M i p
  rw [hv, Category.assoc, Category.assoc, baseInclusionF_baseF, Category.comp_id]

lemma operator_coefficientF (p : ℤ) :
    (operator A M i).v p (p + 1) rfl ≫ coefficientF A M i (p + 1) = 0 := by
  have hv : (operator A M i).v p (p + 1) rfl =
      coefficientF A M i p ≫ i.f (p + 1) ≫ baseInclusionF A M i (p + 1) := operator_v A M i p
  rw [hv, Category.assoc, Category.assoc, baseInclusionF_coefficientF, comp_zero, comp_zero]

lemma complex_d_baseF (p : ℤ) :
    (complex A M i).d p (p + 1) ≫ baseF A M i (p + 1) =
      baseF A M i p ≫ A.X.d p (p + 1) + coefficientF A M i p ≫ i.f (p + 1) := by
  have hc : (splitAlgebra A M).X.d p (p + 1) ≫ baseF A M i (p + 1) =
      baseF A M i p ≫ A.X.d p (p + 1) :=
    ((biprod.fst : (splitAlgebra A M).X ⟶ A.X).comm p (p + 1)).symm
  rw [perturbComplex_d, Preadditive.add_comp, hc, operator_baseF]

lemma complex_d_coefficientF (p : ℤ) :
    (complex A M i).d p (p + 1) ≫ coefficientF A M i (p + 1) =
      -(coefficientF A M i p ≫ M.X.d (p + 1) (p + 1 + 1)) := by
  have hc : (splitAlgebra A M).X.d p (p + 1) ≫ coefficientF A M i (p + 1) =
      coefficientF A M i p ≫ (M.X⟦(1 : ℤ)⟧).d p (p + 1) :=
    ((biprod.snd : (splitAlgebra A M).X ⟶ (DGBimoduleShift.obj M 1).X).comm p (p + 1)).symm
  have hs : (M.X⟦(1 : ℤ)⟧).d p (p + 1) = -M.X.d (p + 1) (p + 1 + 1) := by
    simp only [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_one, Units.neg_smul, one_smul]
  rw [perturbComplex_d, Preadditive.add_comp, hc, operator_coefficientF, add_zero, hs,
    Preadditive.comp_neg]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeCoordinates
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
概要：追加微分の担体と元の cone の担体の、二座標を保つ次数ごとの実同型。
方針：cone の実二包含と直和の実二射影で互いに逆な線形写像を作る。
規約：微分との可換性は後続で検証する。使われ方：Postnikov cone の実複体同型。
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

def gradedToCone (p : ℤ) : (complex A M i).X p ⟶ (mappingCone i).X p :=
  baseF A M i p ≫ (mappingCone.inr i).f p +
    coefficientF A M i p ≫ (mappingCone.inl i).v (p + 1) p (by omega)

def gradedFromCone (p : ℤ) : (mappingCone i).X p ⟶ (complex A M i).X p :=
  (mappingCone.snd i).v p p (add_zero p) ≫ baseInclusionF A M i p +
    (mappingCone.fst i).val.v p (p + 1) rfl ≫ coefficientInclusionF A M i p

@[reassoc] lemma gradedToCone_fst (p : ℤ) :
    gradedToCone A M i p ≫ (mappingCone.fst i).val.v p (p + 1) rfl =
      coefficientF A M i p := by
  simp only [gradedToCone, Preadditive.add_comp, Category.assoc,
    mappingCone.inr_f_fst_v, comp_zero, mappingCone.inl_v_fst_v,
    Category.comp_id, zero_add]

@[reassoc] lemma gradedToCone_snd (p : ℤ) :
    gradedToCone A M i p ≫ (mappingCone.snd i).v p p (add_zero p) = baseF A M i p := by
  simp only [gradedToCone, Preadditive.add_comp, Category.assoc,
    mappingCone.inr_f_snd_v, mappingCone.inl_v_snd_v, comp_zero,
    Category.comp_id, add_zero]

@[reassoc] lemma gradedFromCone_baseF (p : ℤ) :
    gradedFromCone A M i p ≫ baseF A M i p = (mappingCone.snd i).v p p (add_zero p) := by
  simp only [gradedFromCone, Preadditive.add_comp, Category.assoc,
    baseInclusionF_baseF, coefficientInclusionF_baseF, comp_zero,
    Category.comp_id, add_zero]

@[reassoc] lemma gradedFromCone_coefficientF (p : ℤ) :
    gradedFromCone A M i p ≫ coefficientF A M i p =
      (mappingCone.fst i).val.v p (p + 1) rfl := by
  simp only [gradedFromCone, Preadditive.add_comp, Category.assoc,
    baseInclusionF_coefficientF, coefficientInclusionF_coefficientF, comp_zero,
    Category.comp_id, zero_add]

lemma gradedToCone_fromCone (p : ℤ) : gradedToCone A M i p ≫ gradedFromCone A M i p = 𝟙 _ := by
  rw [gradedFromCone, Preadditive.comp_add, ← Category.assoc, gradedToCone_snd,
    ← Category.assoc, gradedToCone_fst, coordinates_total]

lemma gradedFromCone_toCone (p : ℤ) : gradedFromCone A M i p ≫ gradedToCone A M i p = 𝟙 _ := by
  apply mappingCone.ext_to i p (p + 1) rfl
  · rw [Category.assoc, gradedToCone_fst, gradedFromCone_coefficientF, Category.id_comp]
  · rw [Category.assoc, gradedToCone_snd, gradedFromCone_baseF, Category.id_comp]

def gradedIso (p : ℤ) : (complex A M i).X p ≅ (mappingCone i).X p where
  hom := gradedToCone A M i p
  inv := gradedFromCone A M i p
  hom_inv_id := gradedToCone_fromCone A M i p
  inv_hom_id := gradedFromCone_toCone A M i p

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

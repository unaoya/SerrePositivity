module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeGradedIso

/-!
概要：層包含で微分変更した担体と元の mapping cone の、二座標を保つ実複体同型。
方針：微分の二つの行列成分を合わせ、次数ごとの同型を複体の同型へ昇格する。
規約：包含成分の正符号を保持。使われ方：底への全射準同型比較と線形 class の移送。
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

lemma gradedToCone_comm (p : ℤ) :
    gradedToCone A M i p ≫ (mappingCone i).d p (p + 1) =
      (complex A M i).d p (p + 1) ≫ gradedToCone A M i (p + 1) := by
  apply mappingCone.ext_to i (p + 1) (p + 1 + 1) rfl
  · rw [Category.assoc, mappingCone.d_fst_v i p (p + 1) (p + 1 + 1) rfl rfl,
      Preadditive.comp_neg, ← Category.assoc, gradedToCone_fst,
      Category.assoc, gradedToCone_fst, complex_d_coefficientF]
  · rw [Category.assoc, mappingCone.d_snd_v i p (p + 1) rfl, Preadditive.comp_add,
      ← Category.assoc, gradedToCone_fst, ← Category.assoc, gradedToCone_snd,
      Category.assoc, gradedToCone_snd, complex_d_baseF]
    exact add_comm _ _

def complexIso : complex A M i ≅ mappingCone i :=
  HomologicalComplex.Hom.isoOfComponents (gradedIso A M i) (fun p q hpq => by
    obtain rfl : q = p + 1 := hpq.symm
    exact gradedToCone_comm A M i p)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeComplexIso
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
概要：微分変更後の係数座標と標準 cone 三角形の境界を、負符号を保って比較する。
方針：標準境界の shift 定義を各次数で計算し、元の第一射影を回収する。
規約：境界は負の係数座標。使われ方：Postnikov class の元の線形 class との一致。
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

lemma cone_boundary_f (p : ℤ) : (mappingCone.triangle i).mor₃.f p =
    -(mappingCone.fst i).val.v p (p + 1) rfl := by
  simp [mappingCone.triangle, Cocycle.homOf, Cocycle.rightShift, Cochain.rightShift,
    CochainComplex.shiftFunctorObjXIso]

lemma complexIso_boundary_f (p : ℤ) : (complexIso A M i).hom.f p ≫
    (mappingCone.triangle i).mor₃.f p = -coefficientF A M i p := by
  rw [cone_boundary_f, Preadditive.comp_neg]
  exact congrArg Neg.neg (gradedToCone_fst A M i p)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingCurry

/-!
概要：実 AW 制限代数への射と、小さい単体集合からの乗法的写像の同値。
方針：元の全単体で計算し、密度極限の一意性と米田対応で両逆を証明する。
規約：通常の全単体の同値であり、導来写像空間との同一視は別工程。
使われ方：実ホーンの代数的持ち上げを元の全境界を保つ充填へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} {K : SSet.{0}}

lemma smallMultiplicativeMappingTranspose_curry
    (f : A ⟶ (simplicialConvolution R B).obj (op K)) :
    smallMultiplicativeMappingTranspose R (smallMultiplicativeMappingCurry R f) = f := by
  apply (simplexConvolutionDensityCone_isLimit R B K).hom_ext
  intro i
  rw [smallMultiplicativeMappingTranspose_fac, smallMultiplicativeMappingCurry_density]

set_option maxHeartbeats 800000 in -- 選択された実密度極限の射影を元の標準単体の値へ戻す。
lemma smallMultiplicativeMappingCurry_transpose
    (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ multiplicativeMappingSimplices R A B) :
    smallMultiplicativeMappingCurry R (smallMultiplicativeMappingTranspose R a) = a := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change ULift.{u, 0} (K.obj n) at z
  rcases z with ⟨z⟩
  have h := smallMultiplicativeMappingTranspose_fac R a
    (op (CostructuredArrow.mk (SSet.yonedaEquiv.{0}.symm z)))
  change smallMultiplicativeMappingTranspose R a ≫
      (simplicialConvolution R B).map (SSet.yonedaEquiv.{0}.symm z).op =
    a.app n ⟨SSet.yonedaEquiv.{0} (SSet.yonedaEquiv.{0}.symm z)⟩ at h
  rw [SSet.yonedaEquiv.apply_symm_apply] at h
  exact h

def smallMultiplicativeMappingEquiv :
    (A ⟶ (simplicialConvolution R B).obj (op K)) ≃
      (SSet.uliftFunctor.{u, 0}.obj K ⟶ multiplicativeMappingSimplices R A B) where
  toFun := smallMultiplicativeMappingCurry R
  invFun := smallMultiplicativeMappingTranspose R
  left_inv := smallMultiplicativeMappingTranspose_curry R
  right_inv := smallMultiplicativeMappingCurry_transpose R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

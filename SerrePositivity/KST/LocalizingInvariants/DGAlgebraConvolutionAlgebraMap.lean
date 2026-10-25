module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionMaps

/-!
概要：余モノイド射による内部 Hom 前合成の乗法性を構成する。
方針：転置の自然性と同じ対角・余単位の保存を使う。
規約：底の複体射は元の内部 Hom 前合成。
使われ方：実乗法的単体 frame の反変関手性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {H K : Comon (Complex R)}

lemma convolutionPrecompose_one (f : H ⟶ K) (B : Mon (Complex R)) :
    η[((convolutionFunctor R K).obj B).X] ≫ (MonoidalClosed.pre f.hom).app B.X =
      η[((convolutionFunctor R H).obj B).X] := by
  rw [convolutionFunctor_one, convolutionFunctor_one,
    convolutionAdjunction_homEquiv, convolutionAdjunction_homEquiv,
    MonoidalClosed.curry_pre_app]
  congr 1
  rw [← Category.assoc, convolutionTensor_pre_eta]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

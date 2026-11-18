module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplexConstant
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedColimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：任意の小さい単体集合上の実 AW 畳み込み代数と反変極限保存。
方針：実 AW 関手と正本の畳み込みを合成し、底の Hom の保存性を反映する。
規約：元の乗法と元の単体射を保持し、一般の商 API は追加しない。
使われ方：実乗法的単体模型の matching 極限と境界制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def simplicialConvolution (B : Mon (Complex R)) : SSet.{0}ᵒᵖ ⥤ Mon (Complex R) :=
  (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonFunctor R).op ⋙ convolutionContravariant R B

lemma simplicialConvolution_forget (B : Mon (Complex R)) :
    simplicialConvolution R B ⋙ Mon.forget (Complex R) =
      (EInfinity.BarrattEccles.normalizedFunctor R).op ⋙
        MonoidalClosed.internalHom.flip.obj B.X := rfl

instance simplicialConvolution_preservesLimitsOfShape (B : Mon (Complex R))
    (J : Type) [Category.{0} J] : PreservesLimitsOfShape J (simplicialConvolution R B) := by
  have := _root_.SerrePositivity.ComplexLimits.normalizedFunctor_preservesSmallColimits R
  have : PreservesLimitsOfShape J (EInfinity.BarrattEccles.normalizedFunctor R).op :=
    preservesLimitsOfShape_op J _
  let : PreservesLimitsOfShape J (simplicialConvolution R B ⋙ Mon.forget (Complex R)) := by
    rw [simplicialConvolution_forget]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Mon.forget (Complex R))

lemma multiplicativeSimplices_eq_simplicialConvolution (B : Mon (Complex R)) :
    multiplicativeSimplices R B = SSet.stdSimplex.op ⋙ simplicialConvolution R B := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

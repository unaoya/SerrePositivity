module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeSimplices
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
概要：実畳み込みと乗法的単体模型が存在する形状の極限を保つことを示す。
方針：代数の忘却関手の極限創出と内部 Hom の実右随伴性を使う。
規約：局所化後の極限性・Kan 性をこの保存性から仮定しない。
使われ方：元の厳密 Postnikov 錐を同じ単体模型に送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma convolutionFunctor_forget (H : Comon (Complex R)) :
    convolutionFunctor R H ⋙ Mon.forget (Complex R) =
      Mon.forget (Complex R) ⋙ ihom H.X := rfl

instance convolutionFunctor_preservesLimitsOfShape (H : Comon (Complex R))
    (J : Type v) [Category.{w} J] [HasLimitsOfShape J (Complex R)] :
    PreservesLimitsOfShape J (convolutionFunctor R H) := by
  let : PreservesLimitsOfShape J
      (convolutionFunctor R H ⋙ Mon.forget (Complex R)) := by
    rw [convolutionFunctor_forget]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Mon.forget (Complex R))

lemma multiplicativeSimplicesFunctor_evaluation (n : SimplexCategoryᵒᵖ) :
    multiplicativeSimplicesFunctor R ⋙ (evaluation SimplexCategoryᵒᵖ (Mon (Complex R))).obj n =
      convolutionFunctor R
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).obj n.unop) := rfl

instance multiplicativeSimplicesFunctor_preservesLimitsOfShape
    (J : Type v) [Category.{w} J] [HasLimitsOfShape J (Complex R)] :
    PreservesLimitsOfShape J (multiplicativeSimplicesFunctor R) := by
  apply preservesLimitsOfShape_of_evaluation
  intro n
  rw [multiplicativeSimplicesFunctor_evaluation]
  infer_instance

instance multiplicativeMappingFunctor_preservesLimitsOfShape (A : Mon (Complex R))
    (J : Type v) [Category.{w} J] [HasLimitsOfShape J (Complex R)] :
    PreservesLimitsOfShape J (multiplicativeMappingFunctor R A) := by
  unfold multiplicativeMappingFunctor
  infer_instance

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

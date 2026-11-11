module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplicialConvolution
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexReedy
public import SerrePositivity.EInfinity.HomRestriction
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
概要：実乗法的単体代数の matching 制限の底は次数別全射。
方針：実代数の反対図式の latching を標準境界の AW 畳み込みへ比較する。
規約：実代数圏の選択された極限を使用し、代数のモデル構造を仮定しない。
使われ方：AW 単体的 frame の実 Reedy 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

set_option maxHeartbeats 800000 in -- 実代数の latching と反対圏の極限比較を elaboration する。
def multiplicativeMatchingRestriction (B : Mon (Complex R)) (n : SimplexCategory) :=
  ((latchingComparison simplex n).app (multiplicativeSimplices R B).rightOp).unop

lemma multiplicativeSimplices_matching_fibration (B : Mon (Complex R)) (n : SimplexCategory) :
    EInfinity.projectiveFibrations R (multiplicativeMatchingRestriction R B n).hom := by
  let := EInfinity.projectiveModelCategory R
  let F : SSet.{0} ⥤ (Mon (Complex R))ᵒᵖ := (simplicialConvolution R B).rightOp
  let P : MorphismProperty (Mon (Complex R))ᵒᵖ :=
    (cofibrations (Complex R)ᵒᵖ).inverseImage (Mon.forget (Complex R)).op
  change P ((latchingComparison simplex n).app (multiplicativeSimplices R B).rightOp)
  have : PreservesColimitsOfShape (LatchingIndex simplex n) F :=
    preservesColimitsOfShape_rightOp _ (simplicialConvolution R B)
  have hmono : Mono ((latchingComparison simplex n).app SSet.stdSimplex.{0}) := by
    induction n using SimplexCategory.rec with | _ n =>
    rw [← _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.standardBoundaryIso_fac n]
    infer_instance
  have hf : P (F.map ((latchingComparison simplex n).app SSet.stdSimplex)) := by
    change EInfinity.projectiveFibrations R
      ((MonoidalClosed.pre ((EInfinity.BarrattEccles.normalizedFunctor R).map
        ((latchingComparison simplex n).app SSet.stdSimplex))).app B.X)
    rw [convolutionPre_eq_homPrecompose]
    exact EInfinity.homPrecompose_projectiveFibration _
      (EInfinity.ComplexLimits.normalizedMonomorphism_cofibration R _) B.X
  have hd : SSet.stdSimplex ⋙ F = (multiplicativeSimplices R B).rightOp := rfl
  have hi := latchingComparison_preservedIso simplex F SSet.stdSimplex n
  rw [hd] at hi
  exact (P.arrow_iso_iff hi).mpr hf

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

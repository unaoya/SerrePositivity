module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplicialConvolution
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexReedy
public import SerrePositivity.HomologicalAlgebra.Complexes.HomRestriction
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
概要：実 AW 乗法的単体模型の底の複体の Reedy fibrancy。
方針：元の正規化単体の latching と内部 Hom の反変極限保存を合成する。
規約：具体的射影モデルを証明内で使い、モデル構造を入力しない。
使われ方：代数の実 matching 条件への底の比較。
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

def simplexConvolutionUnderlyingDual (B : Mon (Complex R)) :
    SimplexCategory ⥤ (Complex R)ᵒᵖ :=
  (SSet.stdSimplex ⋙ EInfinity.BarrattEccles.normalizedFunctor R) ⋙
    (MonoidalClosed.internalHom.flip.obj B.X).rightOp

lemma simplexConvolutionUnderlyingDual_eq (B : Mon (Complex R)) :
    simplexConvolutionUnderlyingDual R B =
      (multiplicativeSimplices R B ⋙ Mon.forget (Complex R)).rightOp := rfl

lemma simplexConvolutionUnderlyingDual_reedyCofibrant (B : Mon (Complex R)) :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R
    letI : HasLimitsOfSize.{u, u} (Complex R) := ⟨fun _ _ => inferInstance⟩
    reedyLeft simplex (cofibrations (Complex R)ᵒᵖ)
      (initial.to (simplexConvolutionUnderlyingDual R B)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R
  letI : HasLimitsOfSize.{u, u} (Complex R) := ⟨fun _ _ => inferInstance⟩
  let F : Complex R ⥤ (Complex R)ᵒᵖ :=
    (MonoidalClosed.internalHom.flip.obj B.X).rightOp
  have hF : cofibrations (Complex R) ≤ (cofibrations (Complex R)ᵒᵖ).inverseImage F := by
    intro P Q f hf
    change _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R ((MonoidalClosed.pre f).app B.X)
    rw [convolutionPre_eq_homPrecompose]
    exact _root_.SerrePositivity.HomRestriction.homPrecompose_projectiveFibration f hf B.X
  exact reedyCofibrant_of_preservesLatching simplex F
    (SSet.stdSimplex ⋙ EInfinity.BarrattEccles.normalizedFunctor R)
    (fun n => by
      have : PreservesColimitsOfShape (LatchingIndex simplex n) F :=
        preservesColimitsOfShape_rightOp _ (MonoidalClosed.internalHom.flip.obj B.X)
      infer_instance) hF (_root_.SerrePositivity.ComplexLimits.normalizedSimplex_reedyCofibrant R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

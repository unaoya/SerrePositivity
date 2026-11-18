module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CofibrantTensorQuillen
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexReedy
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorAugmentation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation

/-!
# 元の正規化単体テンソル frame の実 Reedy cofibrancy

概要：元の cofibrant X の X⊗N(Δ•) は実射影 Reedy cofibrant。
方針：構成した実テンソル left Quillen 関手で元の正規化単体を送る。
規約：同じ全自然 augmentation と全作用素の擬同型性を保持する。
使われ方：標準 source frame と実 D(R) 写像空間の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

set_option synthInstance.maxHeartbeats 40000 in
lemma normalizedSimplexTensor_reedyCofibrant (X : Complex A)
    (hX : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    reedyLeft simplex (cofibrations (Complex A)) (initial.to (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ComplexLimits.tensorLeft_cofibrant_isLeftQuillen X hX
  have := (ihom.adjunction X).isLeftAdjoint
  exact leftQuillen_frame_reedyCofibrant (tensorLeft X)
    (SSet.stdSimplex ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedSimplex_reedyCofibrant A)

lemma normalizedSimplexTensor_homotopicallyConstant (X : Complex A)
    {n m : SimplexCategory} (f : n ⟶ m) :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    weakEquivalences (Complex A) ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map f) :=
  _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_map_quasiIso A X f

end SerrePositivity.ComplexLimits

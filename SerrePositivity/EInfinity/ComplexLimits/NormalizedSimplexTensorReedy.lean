module

public import SerrePositivity.EInfinity.ComplexLimits.CofibrantTensorQuillen
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexReedy
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorAugmentation
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

lemma normalizedSimplexTensor_reedyCofibrant (X : Complex A)
    (hX : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) :
    letI := projectiveModelCategory A
    reedyLeft simplex (cofibrations (Complex A)) (initial.to (normalizedSimplexTensor A X)) := by
  let := projectiveModelCategory A
  have := tensorLeft_cofibrant_isLeftQuillen X hX
  have := (ihom.adjunction X).isLeftAdjoint
  exact leftQuillen_frame_reedyCofibrant (tensorLeft X)
    (SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A) (normalizedSimplex_reedyCofibrant A)

lemma normalizedSimplexTensor_homotopicallyConstant (X : Complex A)
    {n m : SimplexCategory} (f : n ⟶ m) :
    letI := projectiveModelCategory A
    weakEquivalences (Complex A) ((normalizedSimplexTensor A X).map f) :=
  normalizedSimplexTensor_map_quasiIso A X f

end SerrePositivity.EInfinity.ComplexLimits

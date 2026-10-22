module

public import SerrePositivity.EInfinity.ComplexLimits.CofibrantKProjective
public import SerrePositivity.EInfinity.ComplexLimits.TensorKProjective
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedCochainCofibrant
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorHom

/-!
# 実 cofibrant 始域の正規化単体テンソルの K-projective 性

概要：同じ X⊗N(Δⁿ) は cofibrant X について K-projective。
方針：実 cofibrancy からの K-projective 性と同じテンソルの閉性を合成する。
規約：次数別の射影性や Reedy cofibrancy の代わりにはしない。
使われ方：元の frame 模型の cokernel 判定の高次部分。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma normalizedSimplexTensor_isKProjective (X : Complex A)
    (hX : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) (n : SimplexCategory) :
    CochainComplex.IsKProjective ((normalizedSimplexTensor A X).obj n) := by
  have := projectiveCofibrant_isKProjective X hX
  have := normalizedCochain_isKProjective A (SSet.stdSimplex.obj n)
  exact tensor_isKProjective A X _

end SerrePositivity.EInfinity.ComplexLimits

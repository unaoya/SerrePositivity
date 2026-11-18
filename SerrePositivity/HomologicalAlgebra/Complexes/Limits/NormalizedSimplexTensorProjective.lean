module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CofibrantKProjective
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TensorKProjective
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedCochainCofibrant
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorHom

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CochainComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma normalizedSimplexTensor_isKProjective (X : Complex A)
    (hX : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ X)) (n : SimplexCategory) :
    CochainComplex.IsKProjective ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n) := by
  have := _root_.SerrePositivity.ComplexLimits.projectiveCofibrant_isKProjective X hX
  have := _root_.SerrePositivity.ComplexLimits.normalizedCochain_isKProjective A (SSet.stdSimplex.obj n)
  exact _root_.SerrePositivity.ComplexLimits.tensor_isKProjective A X _

end SerrePositivity.ComplexLimits

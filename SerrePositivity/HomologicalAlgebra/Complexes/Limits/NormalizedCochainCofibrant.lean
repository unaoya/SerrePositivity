module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedChainsFree
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectiveComplexCofibrant

/-!
# 任意の単体集合の実正規化複体の cofibrancy

概要：元の整数次数の正規化鎖は実射影モデルで cofibrant。
方針：全鎖次数の自由表示を延長し、K-projective 性と全障害消滅を使う。
規約：入力単体集合に有限性・可縮性を要求しない。
使われ方：標準単体・境界の実 frame 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CochainComplex _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma normalizedCochain_projective (X : SSet.{0}) (n : ℤ) :
    Projective (((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj X).X n) := by
  have (q : ℕ) : Projective (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)).X q) := _root_.SerrePositivity.ComplexLimits.normalizedChain_projective A X q
  change Projective ((HomologicalComplex.extend _ ComplexShape.embeddingDownNat).X n)
  infer_instance

lemma normalizedCochain_isKProjective (X : SSet.{0}) :
    CochainComplex.IsKProjective ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj X) := by
  have (q : ℕ) : Projective (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)).X q) := _root_.SerrePositivity.ComplexLimits.normalizedChain_projective A X q
  change CochainComplex.IsKProjective (HomologicalComplex.extend _ ComplexShape.embeddingDownNat)
  infer_instance

lemma normalizedCochain_cofibrant (X : SSet.{0}) :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj X) := by
  have (n : ℤ) := _root_.SerrePositivity.ComplexLimits.normalizedCochain_projective A X n
  have := _root_.SerrePositivity.ComplexLimits.normalizedCochain_isKProjective A X
  exact _root_.SerrePositivity.ComplexLimits.projectiveCofibrant_of_isKProjective _

end SerrePositivity.ComplexLimits

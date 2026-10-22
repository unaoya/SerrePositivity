module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedChainsFree
public import SerrePositivity.EInfinity.ComplexLimits.ProjectiveComplexCofibrant

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory CochainComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma normalizedCochain_projective (X : SSet.{0}) (n : ℤ) :
    Projective (((BarrattEccles.normalizedFunctor A).obj X).X n) := by
  have (q : ℕ) : Projective (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((BarrattEccles.linearization A).obj X)).X q) := normalizedChain_projective A X q
  change Projective ((HomologicalComplex.extend _ ComplexShape.embeddingDownNat).X n)
  infer_instance

lemma normalizedCochain_isKProjective (X : SSet.{0}) :
    CochainComplex.IsKProjective ((BarrattEccles.normalizedFunctor A).obj X) := by
  have (q : ℕ) : Projective (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((BarrattEccles.linearization A).obj X)).X q) := normalizedChain_projective A X q
  change CochainComplex.IsKProjective (HomologicalComplex.extend _ ComplexShape.embeddingDownNat)
  infer_instance

lemma normalizedCochain_cofibrant (X : SSet.{0}) :
    (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ (BarrattEccles.normalizedFunctor A).obj X) := by
  have (n : ℤ) := normalizedCochain_projective A X n
  have := normalizedCochain_isKProjective A X
  exact projectiveCofibrant_of_isKProjective _

end SerrePositivity.EInfinity.ComplexLimits

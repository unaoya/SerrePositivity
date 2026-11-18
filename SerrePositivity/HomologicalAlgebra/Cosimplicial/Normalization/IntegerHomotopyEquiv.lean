module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Normalization.NatHomotopyEquiv
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# 指定された整数正規化包含のホモトピー逆

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L21、報告 §399。
同じ自然数複体の包含と逆を元の零延長へ送り、指定homを保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.CosimplicialNormalization
open _root_.CategoryTheory _root_.HomologicalComplex
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- L21：全整数で指定した核の包含そのもののホモトピー同値（Dold–Kan）。 -/
def normalizationHomotopyEquiv :
    HomotopyEquiv ((_root_.SerrePositivity.CosimplicialNormalization.normalizedCochainFunctor A).obj X) ((_root_.SerrePositivity.CosimplicialNormalization.unnormalizedCochainFunctor A).obj X) where
  hom := _root_.SerrePositivity.CosimplicialNormalization.normInclusion A X
  inv := extendMap (_root_.SerrePositivity.CosimplicialNormalization.normalizationRetractionNat A X) ComplexShape.embeddingUpNat
  homotopyHomInvId := by
    apply Homotopy.ofEq
    change extendMap (_root_.SerrePositivity.CosimplicialNormalization.normInclusionNat A X) ComplexShape.embeddingUpNat ≫
      extendMap (_root_.SerrePositivity.CosimplicialNormalization.normalizationRetractionNat A X) ComplexShape.embeddingUpNat = 𝟙 _
    rw [← extendMap_comp, _root_.SerrePositivity.CosimplicialNormalization.normInclusionNat_retraction, extendMap_id]
  homotopyInvHomId := by
    have H := ((_root_.SerrePositivity.CosimplicialNormalization.normalizationHomotopyEquivNat A X).homotopyInvHomId).extend
      ComplexShape.embeddingUpNat
    change Homotopy (extendMap (_root_.SerrePositivity.CosimplicialNormalization.normalizationRetractionNat A X) ComplexShape.embeddingUpNat ≫
      extendMap (_root_.SerrePositivity.CosimplicialNormalization.normInclusionNat A X) ComplexShape.embeddingUpNat) (𝟙 _)
    dsimp only [_root_.SerrePositivity.CosimplicialNormalization.normalizationHomotopyEquivNat] at H
    simpa only [extendMap_comp, extendMap_id] using H

/-- L21：homは別の同型でなく元の指定正規化包含（Dold–Kan）。 -/
lemma normalizationHomotopyEquiv_hom :
    (_root_.SerrePositivity.CosimplicialNormalization.normalizationHomotopyEquiv A X).hom = _root_.SerrePositivity.CosimplicialNormalization.normInclusion A X := rfl

end SerrePositivity.CosimplicialNormalization

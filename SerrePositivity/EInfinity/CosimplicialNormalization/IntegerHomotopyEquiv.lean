module

public import SerrePositivity.EInfinity.CosimplicialNormalization.NatHomotopyEquiv
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
namespace SerrePositivity.EInfinity.CosimplicialNormalization
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- L21：全整数で指定した核の包含そのもののホモトピー同値（Dold–Kan）。 -/
def normalizationHomotopyEquiv :
    HomotopyEquiv ((normalizedCochainFunctor A).obj X) ((unnormalizedCochainFunctor A).obj X) where
  hom := normInclusion A X
  inv := extendMap (normalizationRetractionNat A X) ComplexShape.embeddingUpNat
  homotopyHomInvId := by
    apply Homotopy.ofEq
    change extendMap (normInclusionNat A X) ComplexShape.embeddingUpNat ≫
      extendMap (normalizationRetractionNat A X) ComplexShape.embeddingUpNat = 𝟙 _
    rw [← extendMap_comp, normInclusionNat_retraction, extendMap_id]
  homotopyInvHomId := by
    have H := ((normalizationHomotopyEquivNat A X).homotopyInvHomId).extend
      ComplexShape.embeddingUpNat
    change Homotopy (extendMap (normalizationRetractionNat A X) ComplexShape.embeddingUpNat ≫
      extendMap (normInclusionNat A X) ComplexShape.embeddingUpNat) (𝟙 _)
    dsimp only [normalizationHomotopyEquivNat] at H
    simpa only [extendMap_comp, extendMap_id] using H

/-- L21：homは別の同型でなく元の指定正規化包含（Dold–Kan）。 -/
lemma normalizationHomotopyEquiv_hom :
    (normalizationHomotopyEquiv A X).hom = normInclusion A X := rfl

end SerrePositivity.EInfinity.CosimplicialNormalization

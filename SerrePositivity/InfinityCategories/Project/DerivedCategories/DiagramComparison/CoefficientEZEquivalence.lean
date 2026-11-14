module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleAWProjected
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductEZ

/-!
概要：指定 EZ の逆順ホモトピーを係数変更し、一般係数の自由積比較を両方向の同値にする。
方針：加法関手によるホモトピーの像と、既存の Moore・テンソル・自由化同型を使う。
規約：既存の AW・shuffle を保持し、平坦性や模型構造を追加しない。
使われ方：HA 1.2.4、G10 の正規化テンソルと積重みの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 加法関手の像でも同じ shuffle→AW を恒等へ結ぶ。 -/
def mappedNormalizedShuffleAWHomotopy {B : Type v} [Category.{w} B] [Abelian B]
    (F : ModuleCat.{u} ℤ ⥤ B) [F.Additive]
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    Homotopy (mappedNormalizedShuffle F C D ≫ mappedNormalizedAlexanderWhitney F C D)
      (𝟙 _) := by
  let h := F.mapHomotopy (normalizedShuffleAWHomotopy C D)
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · dsimp only [mappedNormalizedShuffle, mappedNormalizedAlexanderWhitney]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp]
  · exact CategoryTheory.Functor.map_id _ _

variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)

/-- 負次数への延長と指定係数テンソル同型を含む逆順ホモトピー。 -/
def negativeCoefficientShuffleAWHomotopy (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    Homotopy (negativeCoefficientShuffle φ C D ≫ negativeCoefficientAlexanderWhitney φ C D)
      (𝟙 _) := by
  let e := negativeMooreTensorCoefficientIso φ C D
  let h := (((mappedNormalizedShuffleAWHomotopy (integerCoefficientExtension φ) C D).extend
    ComplexShape.embeddingDownNat).compLeft e.inv).compRight e.hom
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · dsimp only [negativeCoefficientShuffle, negativeCoefficientAlexanderWhitney, e]
    simp only [extendMap_comp, Category.assoc]
  · simp only [extendMap_id, Category.comp_id, Iso.inv_hom_id]

/-- 元の A 自由正規化鎖のテンソル上の逆順ホモトピー。 -/
def freeProductShuffleAWHomotopy (X Y : SSet.{u}) :
    Homotopy (freeProductShuffle φ X Y ≫ freeProductAlexanderWhitney φ X Y) (𝟙 _) := by
  let e := tensorIso (integerCoefficientFreeChainsIso φ X) (integerCoefficientFreeChainsIso φ Y)
  let h := ((negativeCoefficientShuffleAWHomotopy φ (linearizedSpace X) (linearizedSpace Y)).compLeft
    e.inv).compRight e.hom
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · dsimp only [freeProductShuffle, freeProductAlexanderWhitney, e]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  · simp only [Category.comp_id, Iso.inv_hom_id]

/-- 元の自由化の指定 AW・shuffle による一般係数の鎖ホモトピー同値。 -/
def freeProductEZEquiv (X Y : SSet.{u}) :
    HomotopyEquiv (freeNegativeChains (A := A) (X ⊗ Y))
      (freeNegativeChains (A := A) X ⊗ freeNegativeChains (A := A) Y) where
  hom := freeProductAlexanderWhitney φ X Y
  inv := freeProductShuffle φ X Y
  homotopyHomInvId := (freeProductEZHomotopy φ X Y).symm
  homotopyInvHomId := freeProductShuffleAWHomotopy φ X Y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

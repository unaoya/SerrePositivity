module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FrameHomHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrameHomotopies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FrameCoactionCounit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductHomComparison
/-!
概要：指定AW・shuffleのHom比較の両合成を恒等射へ結ぶ。
方針：既存の全余単体EZホモトピーに同じ指定余作用とA07を適用する。
規約：IS-W2 A08。元の二射と全パラメータの成分を保持する。
使われ方：HA 1.2.4、正規化重みの指定Hom比較の同値性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type (max u v)) [CommRing A] {J : Type v} [SmallCategory J]
variable (W : J ⥤ SSet.{max u v}) (φ : simplicialRingCoefficient.{max u v} →+* A)
local notation "P" => standardParameterForCoefficients A J
/-- 元の指定shuffle・AWのHom合成は同じ全単体空間の恒等射にホモトピック。 -/
def freeProductHomComparison_homotopy (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    SSet.Homotopy
      ((freeProductHomReverse A W P φ).app Q ≫ (freeProductHomComparison A W P φ).app Q)
      (𝟙 _) := by
  have h := frameHomHomotopyOfChainHomotopy (freeProductFrame A W P) (freeProductFrame A W P)
    (productFrameCoaction A W φ) (productFrameCoaction_counit A W φ)
    (freeProductFrameAW A W P φ ≫ freeProductFrameShuffle A W P φ) (𝟙 _)
    (freeProductFrameAWShuffleHomotopy A W P φ) Q
  convert h using 1 <;> ext n x <;>
    simp [freeProductHomReverse, freeProductHomComparison, cosimplicialHomMap, Category.assoc]
/-- 元の指定AW・shuffleの逆順Hom合成も同じ恒等射にホモトピック。 -/
def freeProductHomReverse_homotopy (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    SSet.Homotopy
      ((freeProductHomComparison A W P φ).app Q ≫ (freeProductHomReverse A W P φ).app Q)
      (𝟙 _) := by
  have h := frameHomHomotopyOfChainHomotopy (freeTensorFrame A W P) (freeTensorFrame A W P)
    (tensorFrameCoaction A W φ) (tensorFrameCoaction_counit A W φ)
    (freeProductFrameShuffle A W P φ ≫ freeProductFrameAW A W P φ) (𝟙 _)
    (freeProductFrameShuffleAWHomotopy A W P φ) Q
  convert h using 1 <;> ext n x <;>
    simp [freeProductHomReverse, freeProductHomComparison, cosimplicialHomMap, Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

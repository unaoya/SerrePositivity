module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalEndpoints
/-!
概要：指定区間の二端点は同じ増大写像の切断になる。
方針：標準単体増大写像の自然性と零単体の同型を使う。
規約：IS-W2 A06の前提計算1。端点と増大写像を保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 指定された区間端点は同じ増大写像の厳密な切断。 -/
theorem normalizedIntervalEndpointChain_augmentation (A : Type u) [CommRing A] (ε : Fin 2) :
    normalizedIntervalEndpointChain A ε ≫
      (normalizedSimplexCochainContraction A ⦋1⦌).hom = 𝟙 _ := by
  letI : IsIso (normalizedSimplexCochainContraction A ⦋0⦌).hom := by
    rw [← SerrePositivity.EInfinity.AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction]
    exact SerrePositivity.EInfinity.AlexanderWhitney.cochainCounit_stdSimplexZero_isIso A
  dsimp only [normalizedIntervalEndpointChain]
  rw [Category.assoc, normalizedSimplexCochainContraction_naturality]
  exact (asIso (normalizedSimplexCochainContraction A ⦋0⦌).hom).inv_hom_id
/-- 全図式の端点も同じ指定増大写像の切断。 -/
theorem normalizedIntervalEndpoint_augmentation (A : Type u) [CommRing A]
    (J : Type v) [Category.{w} J] (ε : Fin 2) :
    normalizedIntervalEndpoint A J ε ≫ (standardParameterAugmentation A J).app ⦋1⦌ = 𝟙 _ := by
  apply NatTrans.ext
  funext j
  change normalizedIntervalEndpointChain A ε ≫
    (normalizedSimplexCochainContraction A ⦋1⦌).hom = 𝟙 _
  exact normalizedIntervalEndpointChain_augmentation A ε
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

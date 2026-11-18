module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
/-!
概要：標準パラメータの定数単体射を同じ増大写像と端点に分解する。
方針：零単体の増大写像の同型と既存増大写像の自然性を使う。
規約：A07の前提計算1/3。既存構成の余単位則。
使われ方：HA 1.2.4、全単体Homの区間射の両端。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type v) [Category.{w} J]
/-- 元の標準パラメータの定数単体射は、同じ増大写像と指定端点の合成。 -/
theorem standardParameter_constant (n : SimplexCategory) (ε : Fin 2) :
    (liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J).map
      (SimplexCategory.const n ⦋1⦌ ε) =
    (standardParameterAugmentation A J).app n ≫ normalizedIntervalEndpoint A J ε := by
  let c := (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A ⦋0⦌).hom
  letI : IsIso c := by
    dsimp only [c]
    rw [← _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction]
    exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplexZero_isIso A
  apply NatTrans.ext
  funext j
  change (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
    (SSet.stdSimplex.map (SimplexCategory.const n ⦋1⦌ ε)) =
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom ≫
        ((asIso c).inv ≫ (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
          (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε)))
  have hc : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
      (SSet.stdSimplex.map (SimplexCategory.const n ⦋0⦌ 0)) =
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom ≫ (asIso c).inv := by
    apply (cancel_mono c).mp
    have hi : (asIso c).inv ≫ c = 𝟙 _ := (asIso c).inv_hom_id
    rw [Category.assoc, hi, Category.comp_id]
    exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction_naturality A (SimplexCategory.const n ⦋0⦌ 0)
  have ht : SimplexCategory.const n ⦋1⦌ ε =
      SimplexCategory.const n ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋1⦌ ε := by
    ext i
    rfl
  rw [ht, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hc, Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

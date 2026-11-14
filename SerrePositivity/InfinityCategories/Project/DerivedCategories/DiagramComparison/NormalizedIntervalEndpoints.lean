module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
public import SerrePositivity.EInfinity.AlexanderWhitney.SimplexCounitContraction
/-!
概要：同じ正規化単体区間への二つの端点を全図式の形で記す。
方針：零単体の指定増大写像の逆と、二つの頂点包含を合成する。
規約：IS-W2 A06の証明の分割。元の正規化模型を使用する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 指定された正規化区間の端点。 -/
def normalizedIntervalEndpointChain (A : Type u) [CommRing A] (ε : Fin 2) :
    𝟙_ (CochainComplex (ModuleCat A) ℤ) ⟶
      freeNegativeChains (A := A)
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌)) := by
  letI : IsIso (normalizedSimplexCochainContraction A ⦋0⦌).hom := by
    rw [← SerrePositivity.EInfinity.AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction]
    exact SerrePositivity.EInfinity.AlexanderWhitney.cochainCounit_stdSimplexZero_isIso A
  exact (asIso (normalizedSimplexCochainContraction A ⦋0⦌).hom).inv ≫
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
      (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε))
/-- 全図式の同じ正規化区間の端点。 -/
def normalizedIntervalEndpoint (A : Type u) [CommRing A]
    (J : Type v) [Category.{w} J] (ε : Fin 2) :
    𝟙_ (J ⥤ CochainComplex (ModuleCat A) ℤ) ⟶
      freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))) where
  app _ := normalizedIntervalEndpointChain A ε
  naturality i j f := by
    change 𝟙 _ ≫ normalizedIntervalEndpointChain A ε =
      normalizedIntervalEndpointChain A ε ≫
        HomologicalComplex.extendMap
          ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map
            (Functor.whiskerRight (𝟙 _) (ModuleCat.free A))) ComplexShape.embeddingDownNat
    erw [Functor.whiskerRight_id', CategoryTheory.Functor.map_id,
      HomologicalComplex.extendMap_id]
    simp only [Category.id_comp, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

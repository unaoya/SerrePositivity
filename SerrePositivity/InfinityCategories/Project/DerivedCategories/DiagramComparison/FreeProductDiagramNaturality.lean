module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramMaps

/-!
概要：自由積 AW・shuffle の全図式射が、二つの単体的図式の射と可換であることを示す。
方針：既存の自由正規化鎖関手を後合成し、各点の指定自然性を使う。
規約：図式の添字方向と重み・標準単体を変える方向をともに保持する。
使われ方：HA 1.2.4、G10 の積重みの全単体作用素との照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J] {A : Type u} [CommRing A]
variable (φ : simplicialRingCoefficient.{u} →+* A)
variable {X X' Y Y' : J ⥤ SSet.{u}}

/-- 元の自由負次数鎖を、図式の自然変換に作用させる。 -/
def freeNegativeChainsDiagramMap (f : X ⟶ X') :
    freeNegativeChainsDiagram (A := A) X ⟶ freeNegativeChainsDiagram (A := A) X' where
  app j := freeNegativeChainsMap (A := A) (f.app j)
  naturality i j t := by
    dsimp only [freeNegativeChainsDiagram, Functor.comp_map]
    change freeNegativeChainsMap (A := A) (X.map t) ≫ _ =
      _ ≫ freeNegativeChainsMap (A := A) (X'.map t)
    simpa only [freeNegativeChainsMap, ← Functor.map_comp, ← extendMap_comp, Functor.whiskerRight_comp] using
      congrArg (fun k => freeNegativeChainsMap (A := A) k) (f.naturality t)

/-- 指定 AW は重み・単体パラメータの全図式射と可換。 -/
@[reassoc]
theorem freeProductDiagramAW_naturality (f : X ⟶ X') (g : Y ⟶ Y') :
    freeNegativeChainsDiagramMap (f ⊗ₘ g) ≫ freeProductDiagramAW φ X' Y' =
      freeProductDiagramAW φ X Y ≫
        (freeNegativeChainsDiagramMap f ⊗ₘ freeNegativeChainsDiagramMap g) := by
  apply NatTrans.ext
  funext j
  exact freeProductAlexanderWhitney_naturality φ (f.app j) (g.app j)

/-- 指定 shuffle も同じ全図式射と可換。 -/
@[reassoc]
theorem freeProductDiagramShuffle_naturality (f : X ⟶ X') (g : Y ⟶ Y') :
    (freeNegativeChainsDiagramMap f ⊗ₘ freeNegativeChainsDiagramMap g) ≫
        freeProductDiagramShuffle φ X' Y' =
      freeProductDiagramShuffle φ X Y ≫ freeNegativeChainsDiagramMap (f ⊗ₘ g) := by
  apply NatTrans.ext
  funext j
  exact freeProductShuffle_naturality φ (f.app j) (g.app j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
public import SerrePositivity.EInfinity.ComplexLimits.TruncatedDoldKanFunctor
public import SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationAdjunction
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
概要：元の自由正規化鎖と実 Dold–Kan 空間の随伴を図式全体に持ち上げる。
方針：自由加群・正規化・負次数延長の既存随伴を合成する。
規約：元の free・Moore 正規化・smart 切断・Γ の関手を保つ。
使われ方：HA 1.2.4、G10 の積重みの Hom と重み付き切断の同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicTopology
open SerrePositivity.HomologicalAlgebra SerrePositivity.EInfinity.ComplexLimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- 元の自由正規化鎖の随伴。 -/
def freeNegativeChainsAdjunction :
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (ModuleCat A)).obj
      (ModuleCat.free A) ⋙ normalizedMooreComplex (ModuleCat A) ⋙
        ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ⊣
      truncatedDoldKanFunctor A :=
  (Adjunction.whiskerRight SimplexCategoryᵒᵖ (ModuleCat.adj A)).comp
    ((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).toAdjunction.comp
        (negativeExtendTruncationAdjunction (ModuleCat A)))

/-- 元の図式自由鎖と、各点の実 Dold–Kan 空間の随伴。 -/
def freeNegativeChainsDiagramAdjunction (J : Type v) [Category.{w} J] :
    freeNegativeChainsDiagramFunctor A J ⊣
      (Functor.whiskeringRight J (CochainComplex (ModuleCat A) ℤ) SSet.{u}).obj
        (truncatedDoldKanFunctor A) :=
  Adjunction.whiskerRight J (freeNegativeChainsAdjunction A)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

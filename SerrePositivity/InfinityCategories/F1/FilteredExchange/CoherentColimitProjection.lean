module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.Core.CoconeFamily
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeEdges
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.Core.RelativeInitialVertices

/-!
概要：全小 coherent 図式の普遍余錐の射影は、実際に自明 Kan 射である。
方針：構成済みの全空間余錐を各図式の指定頂点とし、相対始対象の射影の判定を使う。
規約：filtered 性・底の quasicategory 性は不要。使われ方：余極限関手の実際の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})

/-- 元の関手頂点を、構成済みの全空間余極限余錐の指定頂点で持ち上げる。 -/
def coherentTotalColimitCoconeVertex
    (v : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}) _⦋0⦌) :
    (colimitCocones ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}) _⦋0⦌ :=
  colimitCoconeVertex (coherentDiagramTotalCocone ((functorVertexEquiv _ _).symm v))
    (coherentDiagramTotalCocone_isColimit _)

/-- 指定した全空間余錐は元の図式頂点そのものの上にある。 -/
lemma coherentTotalColimitCoconeVertex_projection
    (v : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}) _⦋0⦌) :
    (colimitCoconeProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}).app
      (Opposite.op ⦋0⦌) (coherentTotalColimitCoconeVertex B v) = v := by
  rw [coherentTotalColimitCoconeVertex, colimitCoconeVertex_projection]
  exact (functorVertexEquiv _ _).apply_symm_apply v

/-- 全小 coherent 図式の普遍余錐の射影は、存在を仮定せず自明 Kan 射となる。 -/
lemma coherentColimitCoconeProjection_trivialKanFibration :
    TrivialKanFibration (colimitCoconeProjection
      ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}) := by
  apply relativeInitialProjection_trivialKanFibration
  intro v
  exact ⟨coherentTotalColimitCoconeVertex B v, coherentTotalColimitCoconeVertex_projection B v⟩

end SerrePositivity.InfinityCategories.F2

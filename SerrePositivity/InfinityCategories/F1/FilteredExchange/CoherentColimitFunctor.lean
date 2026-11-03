module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentColimitProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentColimitSection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Core.CoconeFamily
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.Core.RelativeInitialVertices

/-!
概要：全小 coherent 空間値図式から空間への余極限関手を実際に構成する。
方針：元の全空間余錐を頂点に保つ普遍余錐の切断を、余錐の頂点で評価する。
規約：filtered 性は不要。使われ方：元の指定余極限錐との比較と有限極限の保存。
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

/-- 元の全空間余錐を全頂点で保つ、全 coherent 図式の余錐の関手的な選択。 -/
def coherentColimitCoconeFunctor :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶
      (ihom (join ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (Δ[0] : SSet.{u + 1}))).obj SpaceInfinity.{u} :=
  coherentColimitCoconeSection B ≫
    (relativeInitialVertices (coconeRestriction
      ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u})).ι

/-- 選んだ全余錐の元の図式への制限は厳密に恒等関手。 -/
lemma coherentColimitCoconeFunctor_restrict :
    coherentColimitCoconeFunctor B ≫
      coconeRestriction ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} = 𝟙 _ := by
  simpa only [coherentColimitCoconeFunctor, colimitCoconeProjection,
    relativeInitialProjection, Category.assoc] using coherentColimitCoconeSection_projection B

/-- 各図式での全余錐は、元の構成済みの全空間余錐そのもの。 -/
lemma coherentColimitCoconeFunctor_vertex
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (coherentColimitCoconeFunctor B).app (Opposite.op ⦋0⦌) (functorVertex F) =
      functorVertex (coherentDiagramTotalCocone F).val := by
  change ((coherentColimitCoconeSection B).app (Opposite.op ⦋0⦌) (functorVertex F)).val = _
  rw [coherentColimitCoconeSection_vertex]
  change functorVertex (coherentDiagramTotalCocone
    ((functorVertexEquiv _ _).symm (functorVertex F))).val = _
  have hF : (functorVertexEquiv _ _).symm (functorVertex F) = F :=
    (functorVertexEquiv _ _).symm_apply_apply F
  rw [hF]

/-- 全小 coherent 空間値図式の余極限を与える実際の単体集合の射。 -/
def coherentColimitFunctor :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  coherentColimitCoconeFunctor B ≫ evaluateFunctorAt
    (SSet.yonedaEquiv (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj B) (Δ[0] : SSet.{u + 1})))

/-- 余極限関手は各図式の元の小さい全空間 Kan 模型を厳密に値として持つ。 -/
lemma coherentColimitFunctor_vertex
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (coherentColimitFunctor B).app (Opposite.op ⦋0⦌) (functorVertex F) =
      coherentDiagramTotalVertex F := by
  change (evaluateFunctorAt _).app (Opposite.op ⦋0⦌)
    ((coherentColimitCoconeFunctor B).app (Opposite.op ⦋0⦌) (functorVertex F)) = _
  rw [coherentColimitCoconeFunctor_vertex, evaluateFunctorAt_functorVertex]
  have h := coherentDiagramTotalCocone_vertex F
  rw [JoinCocone.vertex_eq, SSet.yonedaEquiv_comp] at h
  exact h

end SerrePositivity.InfinityCategories.F2

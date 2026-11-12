module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices

/-!
概要：余極限関手を頂点とする、全小 coherent 図式の元の普遍余錐を構成する。
方針：選んだ全余錐の族を二変数交換し、元の各図式の全空間余錐へ厳密に評価する。
規約：全点で余極限性を証明する。使われ方：余極限関手による標準の coherent な完成。
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

/-- 全小 coherent 図式の同時評価図式に対する、元の全空間余錐の自然な普遍余錐。 -/
def coherentColimitUniversalCocone : JoinCocone (internalHomFlipHomEquiv
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u})
    ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} (𝟙 _)) :=
  ⟨internalHomFlipHomEquiv _ _ _ (coherentColimitCoconeFunctor B), by
    rw [← internalHomFlipHomEquiv_pre_app]
    change internalHomFlipHomEquiv _ _ _ (coherentColimitCoconeFunctor B ≫
      coconeRestriction _ _) = _
    rw [coherentColimitCoconeFunctor_restrict]⟩

/-- 同時評価余錐は元の全図式の各点で余極限余錐となる。 -/
lemma coherentColimitUniversalCocone_pointwise :
    IsPointwiseColimitCone (coherentColimitUniversalCocone B) := by
  intro v
  obtain ⟨F, rfl⟩ := (functorVertexEquiv _ _).surjective v
  let K := (SSet.uliftFunctor.{u + 1, u}).obj B
  let A := (ihom K).obj SpaceInfinity.{u}
  let T := join K (Δ[0] : SSet.{u + 1})
  let q := coherentColimitCoconeFunctor B
  have hflip : internalHomFlipHomEquiv T A SpaceInfinity.{u}
      (internalHomFlipHomEquiv A T SpaceInfinity.{u} q) = q :=
    (internalHomFlipHomEquiv A T SpaceInfinity.{u}).left_inv q
  have h := internalHomFlipHomEquiv_app_zero
    (internalHomFlipHomEquiv A T SpaceInfinity.{u} q) (functorVertex F)
  rw [hflip] at h
  change (coherentColimitCoconeFunctor B).app (Opposite.op ⦋0⦌) (functorVertex F) =
    functorVertex (evaluateFunctorCocone (coherentColimitUniversalCocone B)
      (functorVertex F)).val at h
  rw [coherentColimitCoconeFunctor_vertex] at h
  have hv := functorVertex_injective h.symm
  exact (isColimitCone_iff_of_coconeMap_eq _ _ hv).mpr
    (coherentDiagramTotalCocone_isColimit F)

/-- 元の同時評価余錐の頂点は、構成した余極限関手そのもの。 -/
lemma coherentColimitUniversalCocone_vertex :
    (coherentColimitUniversalCocone B).vertex = functorVertex (coherentColimitFunctor B) := by
  rw [JoinCocone.vertex_eq, SSet.yonedaEquiv_comp]
  exact internalHomFlipHomEquiv_app_zero (coherentColimitCoconeFunctor B) _

/-- 元の同時評価余錐は、関手 ∞ 圏でも実際の余極限余錐。 -/
lemma coherentColimitUniversalCocone_isColimit :
    IsColimitCone (coherentColimitUniversalCocone B) :=
  isColimitCone_of_pointwise _ (coherentColimitUniversalCocone_pointwise B)

end SerrePositivity.InfinityCategories.F2

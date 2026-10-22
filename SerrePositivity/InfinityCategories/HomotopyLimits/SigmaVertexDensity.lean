module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaSiftedGeneration
public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedColimitPreservation

/-!
概要：指定された元の P_Σ 頂点自身の、元の小さい元の圏上の全密度余錐を固定する。
方針：既存の全密度余錐を同じ頂点関手へ適用し、包含の単射性で指定頂点へ戻す。
規約：元の図式・全余錐・指定頂点を保持。使われ方：標準左 Kan 余錐との厳密な照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] (v : (SigmaPresheafInfinity C) _⦋0⦌)

omit [Quasicategory C] in
/-- 元の指定頂点から回収した前層関手も、元の P_Σ 条件を満たす。 -/
lemma sigmaVertexPresheaf_mem : IsSigmaPresheaf (functorVertex (sigmaPresheafVertexFunctor v)) :=
  (sigmaPresheafVertexFunctor_vertex v).symm ▸ sigmaPresheafInfinity_vertex v

/-- 元の指定頂点自身を頂点とする、元の小さい元の圏上の全密度余錐。 -/
def sigmaVertexDensityCocone :
    JoinCocone (sigmaElementsYonedaDiagram (sigmaPresheafVertexFunctor v)) :=
  sigmaDensityCocone (sigmaPresheafVertexFunctor v) (sigmaVertexPresheaf_mem v)

/-- 元の全密度余錐の頂点は元の指定頂点そのもの。 -/
lemma sigmaVertexDensityCocone_vertex : (sigmaVertexDensityCocone v).vertex = v := by
  apply Subtype.ext
  exact (sigmaDensityCocone_vertex _ (sigmaVertexPresheaf_mem v)).trans
    (sigmaPresheafVertexFunctor_vertex v)

/-- 元の指定頂点への同じ全密度余錐は余極限。 -/
lemma sigmaVertexDensityCocone_isColimit : IsColimitCone (sigmaVertexDensityCocone v) :=
  sigmaDensityCocone_isColimit _ (sigmaVertexPresheaf_mem v)

/-- sifted 保存関手は、元の指定頂点の同じ全密度余錐を余極限へ送る。 -/
lemma sigmaVertexDensity_image_isColimit
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    {D : SSet.{u + 1}} (G : SigmaPresheafInfinity C ⟶ D)
    (hG : PreservesSmallSiftedColimits G) :
    IsColimitCone (mapJoinCocone G (sigmaVertexDensityCocone v)) := by
  have : IsSiftedInfinity (smallRightUnstraightening (sigmaPresheafVertexFunctor v)) :=
    sigmaPresheafElements_isSifted hC _ (sigmaPresheafVertexFunctor_preservesFiniteProducts v)
  exact hG _ _ _ (sigmaVertexDensityCocone_isColimit v)

end SerrePositivity.InfinityCategories.HomotopyLimits

module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges

/-!
概要：元の固定 Kan 射に沿う、元の全反転 Hom 係数の実 pointed prism を保持する。
方針：元の coherent 辺の全 pointed 族を使い、一般辺の回収と同じ全族を照合する。
規約：元の全係数と実 prism を保持。使われ方：元の長辺の全輸送証人の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の固定射の coherent 辺に沿う、元の全反転 Hom 係数の実 pointed prism。 -/
def pointedCoherentMorphismPrism {K L : KanObject.{u}} (f : K ⟶ L) :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op ⟶ PointedSpaceInfinity.{u} :=
  spaceSimplexPointedFamily (coherentNerveEdge f).edge

/-- 元の全 coherent 単体の厳密な等式は、同じ全 pointed 族の値を保持する。 -/
lemma spaceSimplexPointedFamily_heq_of_eq {n : ℕ} {s t : SpaceInfinity.{u} _⦋n⦌}
    (h : s = t) : HEq (spaceSimplexPointedFamily s) (spaceSimplexPointedFamily t) := by
  subst t
  rfl

/-- 元の Space 辺の全 pointed 族は、元の同じ Kan 射の実 prism と値まで一致する。 -/
lemma spaceEdgePointedFamily_heq_morphism (e : SpaceInfinity.{u} _⦋1⦌) :
    HEq (spaceSimplexPointedFamily e) (pointedCoherentMorphismPrism (coherentEdgeHom e)) :=
  (spaceSimplexPointedFamily_heq_of_eq (coherentEdge_recover e)).symm

end SerrePositivity.InfinityCategories.F2

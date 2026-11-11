module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourcePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeTailExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces

/-!
概要：元の任意の Space 単体に、一点からの Hom の全単体パラメータを前置する。
方針：元の初点退化の head を既存の coneInitialSimplex で取り替え、coslice へ戻す。
規約：元の tail の全 Hom と指定精密化を保持。使われ方：三辺比較の二次整合の同じ四面体。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
  (p : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
    (s.obj ⟨ULift.up 0⟩)).op)

/-- 元の全 Space 単体に、同じ全 Hom パラメータを持つ一点を前置した実拡張単体。 -/
def spaceSimplexPointedAugmentation : SpaceInfinity.{u} _⦋n + 1⦌ :=
  coneInitialSimplex pointKanObject (coherentConeTailExtension s) p

/-- 前置した実頂点は、元の pointed-space 射影で使う同じ一点頂点。 -/
lemma spaceSimplexPointedAugmentation_apex :
    SpaceInfinity.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (spaceSimplexPointedAugmentation s p) = pointSpaceVertex :=
  (coneInitialSimplex_apex pointKanObject (coherentConeTailExtension s) p).trans
    (spaceInfinityVertex_eq_coherent pointKanObject).symm

/-- 前置した一点を除くと、元の全 Space 単体そのものが厳密に回収される。 -/
lemma spaceSimplexPointedAugmentation_tail :
    SpaceInfinity.δ 0 (spaceSimplexPointedAugmentation s p) = s :=
  (coneInitialSimplex_tail pointKanObject (coherentConeTailExtension s) p).trans
    (coherentConeTailExtension_tail s)

/-- 元の全 Space 単体と同じ全 Hom パラメータを持つ、実際の pointed-space 単体。 -/
def spaceSimplexPointedLift : PointedSpaceInfinity.{u} _⦋n⦌ := by
  refine ⟨(leftPointStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (spaceSimplexPointedAugmentation s p), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, spaceSimplexPointedAugmentation_apex]

/-- 構成した実 pointed 単体の射影は、元の全単体を一切変更しない。 -/
lemma spaceSimplexPointedLift_projection :
    pointedSpaceProjection.app (Opposite.op ⦋n⦌) (spaceSimplexPointedLift s p) = s := by
  change SSet.yonedaEquiv (joinInr Δ[0] Δ[n] ≫
    ((leftPointStdSimplexIso n).hom ≫
      SSet.yonedaEquiv.symm (spaceSimplexPointedAugmentation s p))) = s
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inr,
    stdSimplex.δ_comp_yonedaEquiv_symm, spaceSimplexPointedAugmentation_tail,
    Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2

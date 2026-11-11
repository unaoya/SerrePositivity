module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleMaximalPaths
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexStrictification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleComposite

/-!
概要：最大化による strict な三角形の三射を、元の第一射・最後射・二射合成へ戻す。
方針：最大 path に沿う通常の関手の作用を、同じ豊穣零単体の像で計算する。
規約：元の三角形の射を別の代表へ変更しない。
使われ方：最大化側の最後辺の全係数作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "i₀" => ULift.up (0 : Fin 3)
local notation "i₁" => ULift.up (1 : Fin 3)
local notation "i₂" => ULift.up (2 : Fin 3)

/-- 概要：strict な第一射は元の第一射。方針：同じ最大 path の頂点像を計算。
規約：元の射を保持。使われ方：中間係数の作用を固定する。 -/
lemma coherentSimplexStrictDiagram_first_arrow :
    (coherentSimplexStrictDiagram s).map
      (homOfLE (show (i₀ : ULift.{u} (Fin 3)) ≤ i₁ by decide)) =
        coherentEdgeHom (SpaceInfinity.δ 2 s) := by
  let h01 : (i₀ : ULift.{u} (Fin 3)) ≤ i₁ := by decide
  apply (SimplicialCategory.homEquiv' _ _).injective
  change SimplicialCategory.homEquiv' _ _
    ((coherentEnrichedUnderlyingFunctor s).map (coherentMaximalPath h01)) = _
  refine (coherentEnrichedUnderlyingFunctor_vertex s _).trans ?_
  change (s.map ⟨i₀⟩ ⟨i₁⟩).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ (coherentMaximalPath h01)) = _
  rw [coherentTriangleMaximalPath01]
  exact ((SimplicialCategory.homEquiv' _ _).apply_symm_apply _).symm

/-- 概要：strict な最後射は元の最後射。方針：同じ最大 path の頂点像を計算。
規約：元の射を保持。使われ方：最後辺の係数作用を固定する。 -/
lemma coherentSimplexStrictDiagram_last_arrow :
    (coherentSimplexStrictDiagram s).map
      (homOfLE (show (i₁ : ULift.{u} (Fin 3)) ≤ i₂ by decide)) =
        coherentEdgeHom (SpaceInfinity.δ 0 s) := by
  let h12 : (i₁ : ULift.{u} (Fin 3)) ≤ i₂ := by decide
  apply (SimplicialCategory.homEquiv' _ _).injective
  change SimplicialCategory.homEquiv' _ _
    ((coherentEnrichedUnderlyingFunctor s).map (coherentMaximalPath h12)) = _
  refine (coherentEnrichedUnderlyingFunctor_vertex s _).trans ?_
  change (s.map ⟨i₁⟩ ⟨i₂⟩).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ (coherentMaximalPath h12)) = _
  rw [coherentTriangleMaximalPath12]
  exact ((SimplicialCategory.homEquiv' _ _).apply_symm_apply _).symm

/-- 概要：strict な長射は元の二射合成。方針：同じ合成 path の像を計算。
規約：元の二辺を保持。使われ方：Ncomp の全係数の head を照合する。 -/
lemma coherentSimplexStrictDiagram_composite_arrow :
    (coherentSimplexStrictDiagram s).map
      (homOfLE (show (i₀ : ULift.{u} (Fin 3)) ≤ i₂ by decide)) =
        coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s) := by
  let h02 : (i₀ : ULift.{u} (Fin 3)) ≤ i₂ := by decide
  apply (SimplicialCategory.homEquiv' _ _).injective
  change SimplicialCategory.homEquiv' _ _
    ((coherentEnrichedUnderlyingFunctor s).map (coherentMaximalPath h02)) = _
  refine (coherentEnrichedUnderlyingFunctor_vertex s _).trans ?_
  change (s.map ⟨i₀⟩ ⟨i₂⟩).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ (coherentMaximalPath h02)) = _
  rw [coherentTriangleMaximalPath02]
  exact coherentTriangleComposite_image s

end SerrePositivity.InfinityCategories.F2

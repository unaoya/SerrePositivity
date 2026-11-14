module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.HornBoundaryOver

/-!
概要：元の標準単体と、その境界・面・ホーンの底上の包含を束ねる。
方針：同じ標準包含の可換式を底上の圏へ移す。
規約：元の単体写像と全ての包含を保持する。
使われ方：境界の局所 Hom 比較と同じセル比較を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
variable {B : SSet.{u}} (n : ℕ) (i : Fin (n + 2)) (σ : (Δ[n + 1] : SSet.{u}) ⟶ B)

/-- 同じ標準境界から元の単体への包含。 -/
def boundarySimplexOverMap : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex n σ ⟶ Over.mk σ :=
  Over.homMk (boundary (n + 1)).ι rfl

/-- 同じ欠けた面から元の単体への包含。 -/
def faceSimplexOverMap : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.face n i σ ⟶ Over.mk σ :=
  Over.homMk (stdSimplex.δ i) rfl

/-- 同じホーンから元の単体への包含。 -/
def hornSimplexOverMap : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.horn n i σ ⟶ Over.mk σ :=
  Over.homMk (horn (n + 1) i).ι rfl

/-- 面から境界を通る包含は、同じ直接の面包含。 -/
lemma faceSimplexOverMap_comp :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion n i σ ≫ boundarySimplexOverMap n σ =
      faceSimplexOverMap n i σ := by
  apply Over.OverMorphism.ext
  exact boundary.ι_ι i

/-- ホーンから境界を通る包含は、同じ直接のホーン包含。 -/
lemma hornSimplexOverMap_comp :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion n i σ ≫ boundarySimplexOverMap n σ =
      hornSimplexOverMap n i σ := by
  apply Over.OverMorphism.ext
  rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

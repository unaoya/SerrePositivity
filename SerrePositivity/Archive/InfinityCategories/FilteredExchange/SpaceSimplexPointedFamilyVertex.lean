module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：元の全 pointed 族の任意の頂点を、同じ coslice 頂点への全 Hom 前合成で読む。
方針：同じ実頂点包含を豊穣係数の全前合成まで押し込み、定値成分を計算する。
規約：全係数と元の実頂点を保持。使われ方：三頂点の固定 Kan 射の公式の代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 全 pointed 族の頂点は、元の同じ coslice 頂点を全 Hom 係数で前合成した族。 -/
lemma spaceSimplexPointedFamily_vertex {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
    (i : Fin (n + 1)) :
    simplexPrismVertex n i (spaceSimplexPointedCoefficients s) ≫ spaceSimplexPointedFamily s =
    lift (SSet.const ((SSet.yonedaEquiv.symm (spaceSimplexSourceCone s)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i))) (𝟙 (spaceSimplexPointedCoefficients s)) ≫
        coherentCosliceSourcePrecomposition pointKanObject (s.obj ⟨ULift.up 0⟩) ≫
          pointedCoherentCosliceIso.hom := by
  unfold spaceSimplexPointedFamily spaceSimplexCoslicePointedFamily
  simp only [← Category.assoc]
  rw [simplexPrismVertex, lift_whiskerRight, SSet.const_comp]

end SerrePositivity.InfinityCategories.F2

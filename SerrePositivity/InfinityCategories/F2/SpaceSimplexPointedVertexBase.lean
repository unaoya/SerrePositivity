module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedFamilyVertex

/-!
概要：元の全 Space 図式の各頂点の底を、同じ Kan 対象の coherent 表示へ戻す。
方針：全係数を忘れた定値頂点を、coherent 頂点と対象の全単射で同定する。
規約：全係数と実頂点を保持。使われ方：同じ全比較の固定 fiber への評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全図式の指定頂点の底は、同じ元の Kan 対象の coherent 頂点に厳密に定値。 -/
lemma spaceSimplexPointedVertex_base {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
    (i : Fin (n + 1)) :
    simplexPrismVertex n i (spaceSimplexPointedCoefficients s) ≫
        (fst Δ[n] _ ≫ SSet.yonedaEquiv.symm s) =
      SSet.const (coherentNerveVertex (s.obj ⟨ULift.up i⟩)) := by
  rw [simplexPrismVertex, ← Category.assoc, lift_fst, SSet.const_comp]
  have hv : (SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) = coherentNerveVertex (s.obj ⟨ULift.up i⟩) := by
    apply (coherentNerveVertexEquiv KanObject).symm.injective
    rfl
  rw [hv]

end SerrePositivity.InfinityCategories.F2

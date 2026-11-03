module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexSourceConeFaces

/-!
概要：初点 coslice の零面の座標は元の全 Space 単体そのもの。
方針：初点退化の第二頂点を除き、退化と面の単体恒等式を使う。
規約：零面を標準の初点 coslice へ置き換えない。
使われ方：合成比較三単体から得る零面の実 pointed 族の座標。
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

/-- 初点 coslice の零面は、元の全単体を座標として厳密に保持する。 -/
lemma spaceSimplexSourceCone_zero_face_coordinates {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) :
    coherentCosliceSourceSimplex (s.obj ⟨ULift.up 0⟩)
      ((sliceUnder (SSet.yonedaEquiv.symm
        (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).δ 0 (spaceSimplexSourceCone s)) = s := by
  have htail := congrArg (fun t : SpaceInfinity.{u} _⦋n + 2⦌ ↦ SpaceInfinity.δ 1 t)
    (coherentConeTailExtension_eq_sigmaZero s)
  exact (spaceSimplexSourceCone_face_coordinates s 0).trans
    (htail.trans (SSet.δ_comp_σ_succ_apply (S := SpaceInfinity) 0 s))

end SerrePositivity.InfinityCategories.F2

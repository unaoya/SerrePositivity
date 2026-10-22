module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalFiltered

/-!
概要：任意の図式を、指定した同じ終頂点を頂点とする余錐へ延長する。
方針：指定終頂点上の slice 射影の切断を uncurry する。
規約：余錐の頂点は存在する別の頂点で置き換えない。
使われ方：共通の小さい部分複体で、指定した終頂点への coslice の余錐を作る。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ指定終頂点を厳密な頂点とする余錐が存在する。 -/
lemma exists_joinCocone_at_terminal {K X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) (f : K ⟶ X) : ∃ c : JoinCocone f, c.vertex = x := by
  have := (isTerminalVertex_iff_trivialKanFibration x).mp hx
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section
    (sliceOverProjection (SSet.yonedaEquiv.symm x))
  have hf : joinInl K Δ[0] ≫ sliceOverUncurry (f ≫ s) = f := by
    rw [sliceOverUncurry_projection, Category.assoc, hs, Category.comp_id]
  refine ⟨⟨sliceOverUncurry (f ≫ s), hf⟩, ?_⟩
  rw [JoinCocone.vertex_eq, sliceOverUncurry_fixed, SSet.yonedaEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2.Ind

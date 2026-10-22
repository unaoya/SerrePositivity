module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalPointJoinExtension

/-!
概要：指定単体の最後の頂点が終対象なら、点の coslice の境界を同じ単体の上に延長できる。
方針：元の図式を uncurry し、右の指定単体を保つ join の境界延長を curry して戻す。
規約：標的や coslice の quasicategory 性を要求しない。
使われ方：cofinal 性の coslice の終頂点側での充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ最後の終頂点を持つ指定単体の上で、元の coslice 境界を延長できる。 -/
lemma exists_pointCosliceBoundary_lift_over_terminal {X : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
    (a : (boundary n : SSet.{u}) ⟶ sliceUnder p) (b : (Δ[n] : SSet.{u}) ⟶ X)
    (h : a ≫ sliceUnderProjection p = (boundary n).ι ≫ b)
    (ht : IsTerminalVertex (b.app _ (stdSimplex.obj₀Equiv.symm (Fin.last n)))) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ sliceUnder p,
      (boundary n).ι ≫ F = a ∧ F ≫ sliceUnderProjection p = b := by
  have ha : joinInr Δ[0] (boundary n : SSet.{u}) ≫ sliceUnderUncurry a = (boundary n).ι ≫ b := by
    rw [sliceUnderUncurry_projection]
    exact h
  obtain ⟨H, hH, hproj⟩ := exists_pointJoinBoundary_extension_over_terminal n b ht
    (sliceUnderUncurry a) ha
  have hfixed : joinInl Δ[0] Δ[n] ≫ H = p := by
    have hh := congrArg (fun f => joinInl Δ[0] (boundary n : SSet.{u}) ≫ f) hH
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed a)
  refine ⟨sliceUnderCurry H hfixed, ?_, ?_⟩
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hH
  · rw [sliceUnderCurry_projection]
    exact hproj

end SerrePositivity.InfinityCategories.F2.Ind

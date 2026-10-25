module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.EdgeUnderCocone

/-!
概要：自明 Kan 射に沿って指定された最終頂点を持つ全余錐を持ち上げる。
方針：余錐の右頂点包含の単射性で全余錐を充填する。
規約：始域図式を持ち上げると同時に元の最終頂点を厳密に固定する。
使われ方：固定入力を持つ元の filtered 表示の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：指定最終頂点と同じ底の全余錐を持つ持ち上げが存在する。
方針：右余錐点からの射を単射に沿って拡張する。
規約：元の全余錐の像と選んだ頂点を厳密に回収する。
使われ方：固定入力の下の元の対象への filtered 全表示。 -/
lemma exists_cocone_lift_with_vertex {K E B : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] {D : K ⟶ B}
    (c : JoinCocone D) (t : E _⦋0⦌)
    (ht : p.app (Opposite.op ⦋0⦌) t = c.vertex) :
    ∃ D' : K ⟶ E, ∃ c' : JoinCocone D',
      c'.val ≫ p = c.val ∧ c'.vertex = t := by
  have : HasLiftingProperty (joinInr K (Δ[0] : SSet.{u})) p :=
    TrivialKanFibration.mem _ (inferInstanceAs (Mono (joinInr K Δ[0])))
  have h : SSet.yonedaEquiv.symm t ≫ p = joinInr K Δ[0] ≫ c.val := by
    rw [SSet.yonedaEquiv_symm_comp, ht, JoinCocone.vertex_eq, Equiv.symm_apply_apply]
  let sq : CommSq (SSet.yonedaEquiv.symm t) (joinInr K Δ[0]) p c.val := ⟨h⟩
  refine ⟨joinInl K Δ[0] ≫ sq.lift, ⟨sq.lift, rfl⟩, sq.fac_right, ?_⟩
  change SSet.yonedaEquiv (joinInr K Δ[0] ≫ sq.lift) = t
  rw [sq.fac_left, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

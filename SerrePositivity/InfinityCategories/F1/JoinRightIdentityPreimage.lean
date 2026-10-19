module

public import SerrePositivity.InfinityCategories.F1.JoinInitialVertexDetection
public import SerrePositivity.InfinityCategories.F1.JoinExtremeFaces

/-!
概要：右因子を保つ joinMap の単体の持ち上げを任意の切断で構成する。
方針：指定単体の右因子を保ち左因子だけを持ち上げる。
規約：切断一に制限せず最後の面から左因子を復元する。
使われ方：射の区間実現の混合ホーンの充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左因子を指定して右因子を保つ joinMap の逆像単体を構成する。
方針：切断と右因子を指定単体からそのまま取り出す。
規約：空の左因子や右因子も含む。
使われ方：混合ホーンの指定像を保つ充填の候補。 -/
lemma Join.Simplex.exists_preimage_right_id {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (t : Join.Simplex X' Y n) (x : Join.augObj X t.1.val)
    (hx : Join.augHom f t.1.val x = t.2.1) :
    ∃ s : Join.Simplex X Y n, s.1 = t.1 ∧ HEq s.2.1 x ∧
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s = t := by
  refine ⟨⟨t.1, x, t.2.2⟩, rfl, HEq.rfl, ?_⟩
  refine Join.Simplex.ext ((joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌)
    ⟨t.1, x, t.2.2⟩) t (by rfl) ?_ ?_
  · exact hx
  · exact Join.augHom_id Y _ _

/-- 概要：最後の面の逆像から任意の混合単体の逆像を得る。
方針：最後の面が保つ左因子を次数の等式で移送して前の構成へ渡す。
規約：切断が最後の頂点以前にあることを必要とする。
使われ方：最後の面を含む左ホーンの充填候補。 -/
lemma Join.Simplex.exists_preimage_right_id_of_last_face {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (t : Join.Simplex X' Y (n + 1)) (ht : t.1.val ≤ n + 1)
    (v : Join.Simplex X Y n) (hv : v.1.val = t.1.val)
    (hface : (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) v =
      Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t) :
    ∃ s : Join.Simplex X Y (n + 1), s.1 = t.1 ∧ HEq s.2.1 v.2.1 ∧
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) s = t := by
  let x : Join.augObj X t.1.val := cast (congrArg (Join.augObj X) hv) v.2.1
  have hleft : HEq (Join.augHom f v.1.val v.2.1)
      (Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t).2.1 := by
    change HEq ((joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) v).2.1 _
    rw [hface]
  have hx : Join.augHom f t.1.val x = t.2.1 := by
    have he := Join.augHom_cast f hv v.2.1
    exact eq_of_heq ((heq_of_eq he.symm).trans ((cast_heq _ _).trans
      (hleft.trans (Join.simplexMap_delta_last_left_heq t ht))))
  obtain ⟨s, hs, hsx, hst⟩ := Join.Simplex.exists_preimage_right_id f t x hx
  exact ⟨s, hs, hsx.trans (cast_heq _ _), hst⟩

end SerrePositivity.InfinityCategories

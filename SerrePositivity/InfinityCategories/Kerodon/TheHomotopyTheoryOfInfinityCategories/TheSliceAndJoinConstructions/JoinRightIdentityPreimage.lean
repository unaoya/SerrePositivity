module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinInitialVertexDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinExtremeFaces

/-!
概要：右因子を保つ joinMap の単体の持ち上げを任意の切断で構成する。
方針：指定単体の右因子を保ち左因子だけを持ち上げる。
規約：切断一に制限せず最後の面から左因子を復元する。
使われ方：射の区間実現の混合ホーンの充填。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：左因子を指定して右因子を保つ joinMap の逆像単体を構成する。
方針：切断と右因子を指定単体からそのまま取り出す。
規約：空の左因子や右因子も含む。
使われ方：混合ホーンの指定像を保つ充填の候補。 -/
lemma Join.Simplex.exists_preimage_right_id {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X' Y n) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X t.1.val)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f t.1.val x = t.2.1) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y n, s.1 = t.1 ∧ HEq s.2.1 x ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s = t := by
  refine ⟨⟨t.1, x, t.2.2⟩, rfl, HEq.rfl, ?_⟩
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌)
    ⟨t.1, x, t.2.2⟩) t (by rfl) ?_ ?_
  · exact hx
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id Y _ _

/-- 概要：最後の面の逆像から任意の混合単体の逆像を得る。
方針：最後の面が保つ左因子を次数の等式で移送して前の構成へ渡す。
規約：切断が最後の頂点以前にあることを必要とする。
使われ方：最後の面を含む左ホーンの充填候補。 -/
lemma Join.Simplex.exists_preimage_right_id_of_last_face {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X' Y (n + 1)) (ht : t.1.val ≤ n + 1)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y n) (hv : v.1.val = t.1.val)
    (hface : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1), s.1 = t.1 ∧ HEq s.2.1 v.2.1 ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) s = t := by
  let x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X t.1.val := cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X) hv) v.2.1
  have hleft : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f v.1.val v.2.1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t).2.1 := by
    change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) v).2.1 _
    rw [hface]
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f t.1.val x = t.2.1 := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_cast f hv v.2.1
    exact eq_of_heq ((heq_of_eq he.symm).trans ((cast_heq _ _).trans
      (hleft.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq t ht))))
  obtain ⟨s, hs, hsx, hst⟩ := Join.Simplex.exists_preimage_right_id f t x hx
  exact ⟨s, hs, hsx.trans (cast_heq _ _), hst⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

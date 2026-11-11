module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinInitialVertexDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinExtremeFaces

/-!
概要：右因子を保つ joinMap の持ち上げと最後の面による検出。
方針：右係数を像から固定し、左係数を最後の面から復元する。
規約：左因子の射の単射性や充填性は要求しない。
使われ方：相対 join の底上の cocartesian 辺を扱う混合外ホーンの充填。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：右因子を保つ joinMap の単体の持ち上げは左係数の持ち上げから作れる。
方針：像の切断と右係数を保持し、指定した左係数を組にする。
規約：空の左係数も含む任意の切断を許す。
使われ方：混合外ホーンの最後の面の左係数から全単体を組み立てる。 -/
lemma joinSimplex_exists_preimage_of_left {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X' Y n) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X t.1.val)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f t.1.val x = t.2.1) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y n, s.1 = t.1 ∧ HEq s.2.1 x ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s = t := by
  refine ⟨⟨t.1, x, t.2.2⟩, rfl, HEq.rfl, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) ⟨t.1, x, t.2.2⟩) t rfl
  · exact hx
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id Y _ _

/-- 概要：右因子が空でない単体は joinMap の像と最後の面で決まる。
方針：最後の面で左係数の HEq を復元し、右係数を像で検出する。
規約：切断の一致は像の等式から回収する。
使われ方：混合外ホーンの各面が構成した充填と一致することの検査。 -/
lemma joinSimplex_ext_of_last_face_joinMap {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1)) (hs : s.1.val ≤ n + 1)
    (hface : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t)
    (hf : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) s =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) t) : s = t := by
  have hc : s.1 = t.1 :=
    congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X' Y (n + 1) ↦ z.1) hf
  have ht : t.1.val ≤ n + 1 := by rw [← hc]; exact hs
  have hh : HEq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom s).2.1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t).2.1 := by
    rw [hface]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_joinMap_right_id f s t
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq s hs).symm.trans
      (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq t ht))) hf

/-- 概要：標準単体から join への射は joinMap の像と最後の面で検出できる。
方針：Yoneda の自然性で単体の検出補題に移す。
規約：右係数は少なくとも一頂点を持つ。
使われ方：外ホーンの各面の厳密な一致。 -/
lemma joinHom_ext_of_last_face_joinMap {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') {a b : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y}
    (ha : (SSet.yonedaEquiv a).1.val ≤ n + 1)
    (hface : stdSimplex.δ (Fin.last (n + 1)) ≫ a =
      stdSimplex.δ (Fin.last (n + 1)) ≫ b)
    (hf : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) : a = b := by
  apply SSet.yonedaEquiv.injective
  apply joinSimplex_ext_of_last_face_joinMap f _ _ ha
  · have h := congrArg SSet.yonedaEquiv hface
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at h
    exact h
  · simpa only [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv hf

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

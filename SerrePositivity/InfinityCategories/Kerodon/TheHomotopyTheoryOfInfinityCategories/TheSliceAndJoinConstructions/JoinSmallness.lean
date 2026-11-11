module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import Mathlib.Logic.Small.Basic

/-!
概要：次数ごとの小ささを保つ単体集合の join と、その頂点の被覆。
方針：切断位置の有限和で小ささを示し、零次の二つの切断を左右の包含に分ける。
規約：小ささの宇宙は単体集合自身の宇宙より小さくてもよい。
使われ方：Kerodon §5.5.2（Tag 01ZV）、Corollary 5.6.0.6（Tag 028T）、coslice の単体の小ささの入力。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：空単体を補っても各次数の小ささは保たれる。
方針：零次の頂点数では一点、正の頂点数では元の単体の小ささを使う。
規約：r は単体の次数でなく頂点数。
使われ方：Kerodon §4.3.5（Tag 017V）、join の次数ごとの小ささ。 -/
instance join_augObj_small (K : SSet.{v}) [∀ n, Small.{u} (K.obj n)] (r : ℕ) :
    Small.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r) := by
  cases r with
  | zero => exact inferInstanceAs (Small.{u} PUnit)
  | succ r => exact inferInstanceAs (Small.{u} (K _⦋r⦌))

/-- 概要：各次数で小さい二つの単体集合の join も各次数で小さい。
方針：切断の有限和と左右の補った単体の積の小ささを使う。
規約：join の元の宇宙 v と小ささの宇宙 u は独立。
使われ方：Kerodon §4.3.5（Tag 017V）、coherent nerve への join からの写像の小さい符号化。 -/
instance join_obj_small (K L : SSet.{v})
    [∀ n, Small.{u} (K.obj n)] [∀ n, Small.{u} (L.obj n)] (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).obj n) := by
  change Small.{u} (Σ ℓ : Fin (n.unop.len + 2),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K ℓ.val × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L (n.unop.len + 1 - ℓ.val))
  infer_instance

/-- 概要：join の全ての頂点は左右どちらかの因子の包含から得られる。
方針：零次の切断位置は零または一なので、それぞれ右または左の頂点を取る。
規約：二つの因子の非空性を仮定しない。
使われ方：Kerodon §5.5.2（Tag 01ZV）、coslice の制限が全頂点の対象を固定することの検証。 -/
lemma join_vertices_covered (K L : SSet.{v}) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) _⦋0⦌) :
    (∃ y, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L).app (Opposite.op ⦋0⦌) y = x) ∨
      (∃ z, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L).app (Opposite.op ⦋0⦌) z = x) := by
  rcases x with ⟨ℓ, x, y⟩
  fin_cases ℓ
  · right
    exact ⟨y, by cases x; rfl⟩
  · left
    exact ⟨x, by cases y; rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

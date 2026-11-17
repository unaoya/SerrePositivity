module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCells
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthRefinement
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentWidth

/-!
概要：まとめた実親について、幅と指定面の実添字・元の全関手の等式を保持する。
方針：元の二つの実親の法則を、同じ実生成元の型へ場合分けで移す。
規約：指定面と幅を親の追加の証人として入力しない。
使われ方：Riehl–Verity Definition 4.2.1・Proposition 4.2.15、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実付着の指定面。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実親の幅は、plus始点では1増え、minus始点では保存される。
方針：元の実終端の親と実最初の細分の幅の法則へ戻す。
規約：全次数の実生成元。使われ方：Riehl–Verity §4.2の実親の幅の比較。 -/
lemma WalkingAdjunctionAtomicCell.parent_width {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    walkingAdjunctionOrdinalWidth (a.parent hnf).chain = walkingAdjunctionOrdinalWidth a.chain +
      (match X with | .plus => 1 | .minus => 0) := by
  cases X with
  | plus => exact walkingAdjunctionPlusParent_ordinalWidth a.chain a.atomic
  | minus =>
    cases n with
    | zero => exact False.elim (hnf trivial)
    | succ n =>
      exact (walkingAdjunctionFirstRefinement_ordinalWidth
        a.chain a.atomic a.nondegenerate).trans (Nat.add_zero _).symm

/-- 概要：実親の指定面の実添字。
方針：plus始点は最後、minus始点は実最小元の直後を使う。
規約：存在を仮定せず元の実構成から取る。使われ方：Riehl–Verity §4.2の実親の深さ。 -/
def WalkingAdjunctionAtomicCell.parentFaceIndex {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) : Fin (n + 2) := by
  cases X with
  | plus => exact Fin.last (n + 1)
  | minus =>
    cases n with
    | zero => exact False.elim (hnf trivial)
    | succ n => exact (walkingAdjunctionFirstBottomMergeIndex a.chain
        (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate).succ.castSucc

/-- 概要：元の生成元を実親の指定面のHomへ写した実全関手。
方針：plus始点には実生成射を前置し、minus始点では元の実全関手を使う。
規約：指定面の元の実射も全て保持。使われ方：Riehl–Verity §4.2の実親と子の境界の照合。 -/
def WalkingAdjunctionAtomicCell.parentChildImage {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) :
    ComposableArrows (walkingAdjunctionHom .minus Y) n :=
  match X, a with
  | .plus, a => walkingAdjunctionPlusParentPrefix a.chain
  | .minus, a => a.chain

/-- 概要：実親の指定した面は、元の実生成元の像の全関手そのもの。
方針：実添字と実親を元の二つの実構成へ戻し、構成済みの実面の等式を使う。
規約：全実関手の等式。使われ方：Riehl–Verity §4.2の実付着の指定面。 -/
lemma WalkingAdjunctionAtomicCell.parent_face {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    finiteChainFace (a.parent hnf).chain (a.parentFaceIndex hnf) = a.parentChildImage := by
  cases X with
  | plus => exact walkingAdjunctionPlusParent_face_last a.chain a.atomic
  | minus =>
    cases n with
    | zero => exact False.elim (hnf trivial)
    | succ n => exact walkingAdjunctionFirstRefinement_face a.chain a.atomic a.nondegenerate

end SerrePositivity.InfinityCategories.HA.Monads

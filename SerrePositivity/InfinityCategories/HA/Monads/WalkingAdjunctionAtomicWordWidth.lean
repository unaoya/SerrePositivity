module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthHorizontal
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicWords

/-!
概要：実原子分解の全因子の幅の和を、元の全実鎖の有限順序の幅へ戻す。
方針：空の実語の幅を0と計算し、水平合成の加法性を実語に帰納する。
規約：幅の等式は実語の括弧の選択によらない。原典の文字列との比較は別に行う。
使われ方：Riehl–Verity Proposition 4.2.15、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの因子の幅の境界。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実単位の有限順序の個数はその端点の補正。
方針：二つの実単位を計算する。規約：空の有限順序も含む。
使われ方：Riehl–Verity §4.2の空の実語の幅。 -/
lemma walkingAdjunctionIdentity_card (X : WalkingAdjunctionPoint) :
    walkingAdjunctionOrdinalCard X X (walkingAdjunctionIdentity X) =
      walkingAdjunctionTargetCorrection X := by
  cases X <;> rfl

/-- 概要：全次数の実単位の有限順序の幅は0。
方針：全辺が実恒等射なので変化量は0であり、端点の補正が個数を相殺する。
規約：元の次数付き圏の単位。使われ方：Riehl–Verity §4.2の空の実原子分解。 -/
lemma walkingAdjunctionOrdinalWidth_id (n : ℕ) (X : WalkingAdjunctionLevel n) :
    walkingAdjunctionOrdinalWidth (𝟙 X : X ⟶ X) = 0 := by
  change walkingAdjunctionOrdinalWidth
    ((Functor.const (Fin (n + 1))).obj (walkingAdjunctionIdentity X.point)) = 0
  simp only [walkingAdjunctionOrdinalWidth, Functor.const_obj_obj, Functor.const_obj_map,
    walkingAdjunctionOrderHom_id, ordinalMapVariation_id, Finset.sum_const_zero,
    walkingAdjunctionIdentity_card, Nat.sub_self, Nat.add_zero]

/-- 概要：実原子的な語の葉の有限順序の幅の和。
方針：空の語では0、実原子ではその幅、合成では和を取る。
規約：元の実射を添字として保持する。使われ方：Riehl–Verity §4.2の実因子の幅。 -/
def WalkingAdjunctionAtomicWord.ordinalWidth {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F) : ℕ :=
  match a with
  | .nil _ => 0
  | .atom F _ => walkingAdjunctionOrdinalWidth F
  | .comp a b => a.ordinalWidth + b.ordinalWidth

/-- 概要：任意の実原子分解の葉の幅の和は、元の実射の幅に等しい。
方針：実語に帰納し、元の実水平合成の幅の加法性を適用する。
規約：分解や括弧の選択を仮定しない。使われ方：Riehl–Verity Proposition 4.2.15。 -/
lemma WalkingAdjunctionAtomicWord.ordinalWidth_eq {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F) :
    a.ordinalWidth = walkingAdjunctionOrdinalWidth F := by
  induction a with
  | nil X => exact (walkingAdjunctionOrdinalWidth_id n X).symm
  | atom F h => rfl
  | @comp X Y Z F G a b ha hb =>
    exact (congrArg₂ (fun x y : ℕ => x + y) ha hb).trans
      (walkingAdjunctionOrdinalWidth_horizontal X.point Y.point Z.point F G).symm

/-- 概要：同じ実射の任意の二つの実原子分解は、葉の幅の和が等しい。
方針：どちらも元の実射の幅に戻す。規約：実語の括弧も任意。
使われ方：Riehl–Verity §4.2の分解によらない実filtrationの幅。 -/
lemma WalkingAdjunctionAtomicWord.ordinalWidth_independent {n : ℕ}
    {X Y : WalkingAdjunctionLevel n} {F : X ⟶ Y}
    (a b : WalkingAdjunctionAtomicWord n F) : a.ordinalWidth = b.ordinalWidth :=
  a.ordinalWidth_eq.trans b.ordinalWidth_eq.symm

/-- 概要：実水平分解の左の実因子の幅は元の実鎖の幅以下。
方針：左右の実因子の幅の和を元の幅へ戻す。
規約：全次数の全実分解。使われ方：Riehl–Verity §4.2の実面の原子分解の境界。 -/
lemma WalkingAdjunctionFactorization.left_ordinalWidth_le {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth a.left ≤ walkingAdjunctionOrdinalWidth H := by
  rw [a.ordinalWidth]
  exact Nat.le_add_right _ _

/-- 概要：実水平分解の右の実因子の幅は元の実鎖の幅以下。
方針：左右の実因子の幅の和を元の幅へ戻す。
規約：全次数の全実分解。使われ方：Riehl–Verity §4.2の実面の原子分解の境界。 -/
lemma WalkingAdjunctionFactorization.right_ordinalWidth_le {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth a.right ≤ walkingAdjunctionOrdinalWidth H := by
  rw [a.ordinalWidth]
  exact Nat.le_add_left _ _

end SerrePositivity.InfinityCategories.HA.Monads

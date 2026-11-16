module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicWordWidth

/-!
概要：有限順序の幅0は実単位を検出し、非自明な実因子の幅は元の幅より小さい。
方針：構成済みの実原子分解と幅の加法性から、0と正値を元の実長さへ戻す。
規約：幅の正値を因子分解の新しい入力にしない。
使われ方：Riehl–Verity Proposition 4.2.15の実filtration、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子分解の厳密な幅の境界。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：任意の実原子分解について、元の幅0なら元の実長さも0。
方針：実原子の幅は1以上、合成の幅は加法的であることを使って実語に帰納する。
規約：実長さは全実頂点の生成語の長さの和。使われ方：Riehl–Verity §4.2の単位の検出。 -/
lemma WalkingAdjunctionAtomicWord.size_zero_of_ordinalWidth_zero {n : ℕ}
    {X Y : WalkingAdjunctionLevel n} {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F)
    (h : walkingAdjunctionOrdinalWidth F = 0) : walkingAdjunctionLevelSize F = 0 := by
  induction a with
  | nil X => exact walkingAdjunctionLevelSize_id n X.point
  | atom F ha =>
    have hw := walkingAdjunctionOrdinalWidth_atomic F ha
    omega
  | @comp X Y Z F G a b ha hb =>
    have hw := walkingAdjunctionOrdinalWidth_horizontal X.point Y.point Z.point F G
    change walkingAdjunctionOrdinalWidth (F ≫ G : X ⟶ Z) =
      walkingAdjunctionOrdinalWidth F + walkingAdjunctionOrdinalWidth G at hw
    have hf : walkingAdjunctionOrdinalWidth F = 0 := by omega
    have hg : walkingAdjunctionOrdinalWidth G = 0 := by omega
    change walkingAdjunctionLevelSize
      (F.prod' G ⋙ walkingAdjunctionHorizontal X.point Y.point Z.point) = 0
    rw [walkingAdjunctionLevelSize_comp X.point Y.point Z.point, ha hf, hb hg]

/-- 概要：全実鎖の幅が0であることは、元の実長さが0であることと同値。
方針：実原子分解を取り、逆向きは実長さ0で実単位へ戻す。
規約：元の全実関手を保持する。使われ方：Riehl–Verity §4.2の空の実分解の検出。 -/
lemma walkingAdjunctionOrdinalWidth_zero_iff_size_zero {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) n) :
    walkingAdjunctionOrdinalWidth H = 0 ↔ walkingAdjunctionLevelSize H = 0 := by
  constructor
  · exact (Classical.choice (walkingAdjunctionAtomicWord_nonempty
      (X := ⟨X⟩) (Y := ⟨Y⟩) H)).size_zero_of_ordinalWidth_zero
  · intro h
    have he := walkingAdjunctionLevelSize_zero_endpoints H h
    subst Y
    rw [walkingAdjunctionLevelSize_zero_eq_id H h]
    exact walkingAdjunctionOrdinalWidth_id n ⟨X⟩

/-- 概要：元の実長さが正であることは、有限順序の幅が正であることと同値。
方針：幅0と実長さ0の検出を自然数の正値へ移す。
規約：全次数の全実鎖。使われ方：Riehl–Verity §4.2の非自明な因子の幅。 -/
lemma walkingAdjunctionOrdinalWidth_pos_iff_size_pos {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) n) :
    0 < walkingAdjunctionOrdinalWidth H ↔ 0 < walkingAdjunctionLevelSize H := by
  have h := walkingAdjunctionOrdinalWidth_zero_iff_size_zero H
  omega

/-- 概要：右因子が非自明な実水平分解では、左因子の幅は元の幅より小さい。
方針：右因子の実長さの正値を幅の正値へ移し、実加法性を使う。
規約：右因子の幅の条件を仮定しない。使われ方：Riehl–Verity §4.2の実面の順序づけ。 -/
lemma WalkingAdjunctionFactorization.left_ordinalWidth_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) (h : 0 < walkingAdjunctionLevelSize a.right) :
    walkingAdjunctionOrdinalWidth a.left < walkingAdjunctionOrdinalWidth H := by
  have hp := (walkingAdjunctionOrdinalWidth_pos_iff_size_pos a.right).mpr h
  rw [a.ordinalWidth]
  omega

/-- 概要：左因子が非自明な実水平分解では、右因子の幅は元の幅より小さい。
方針：左因子の実長さの正値を幅の正値へ移し、実加法性を使う。
規約：左因子の幅の条件を仮定しない。使われ方：Riehl–Verity §4.2の実面の順序づけ。 -/
lemma WalkingAdjunctionFactorization.right_ordinalWidth_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) (h : 0 < walkingAdjunctionLevelSize a.left) :
    walkingAdjunctionOrdinalWidth a.right < walkingAdjunctionOrdinalWidth H := by
  have hp := (walkingAdjunctionOrdinalWidth_pos_iff_size_pos a.left).mpr h
  rw [a.ordinalWidth]
  omega

end SerrePositivity.InfinityCategories.HA.Monads

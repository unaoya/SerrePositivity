module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOnePointDegeneracy
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionLastFaceAtomicity

/-!
概要：minus自己Homの一点の実対象から出る実鎖は、実単位の定値関手となる。
方針：共通表示の最小元と最大元の保存で一点性を終点へ移す。
規約：元の実対象・射・全関手を保持する。
使われ方：Riehl–Verity Proposition 4.2.15の先頭の純粋な実併合の境界、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実単位の回収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：minus自己Homで一点から出る実射の終点も一点。
方針：唯一の点が最小元かつ最大元なので、両方の保存則を比較する。
規約：元の実Homの射。使われ方：Riehl–Verity §4.2の先頭の実単位からの全鎖。 -/
lemma walkingAdjunctionMinusHom_target_card_one
    {A B : walkingAdjunctionHom .minus .minus} (f : A ⟶ B)
    (ha : walkingAdjunctionOrdinalCard .minus .minus A = 1) :
    walkingAdjunctionOrdinalCard .minus .minus B = 1 := by
  let i : Fin (walkingAdjunctionOrdinalCard .minus .minus A) := ⟨0, by omega⟩
  have hb := walkingAdjunctionOrderHom_bottom f i rfl
  have ht := walkingAdjunctionOrderHom_top f i (by change 0 + 1 = _; exact ha.symm)
  omega

/-- 概要：minus自己Homで始点が一点の実鎖は、同じ実単位の定値関手。
方針：始点から全頂点への実射で一点性を回収し、元の定値関手の検収へ移す。
規約：全関手の等式。使われ方：Riehl–Verity §4.2の先頭の境界面の実単位。 -/
lemma walkingAdjunctionMinusChain_eq_identity_of_first_card_one {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .minus) n)
    (hc : walkingAdjunctionOrdinalCard .minus .minus (H.obj 0) = 1) :
    H = (Functor.const (Fin (n + 1))).obj (walkingAdjunctionIdentity .minus) := by
  have hcards (i : Fin (n + 1)) : walkingAdjunctionOrdinalCard .minus .minus (H.obj i) = 1 :=
    walkingAdjunctionMinusHom_target_card_one (H.map (homOfLE (Fin.zero_le i))) hc
  have ho : H.obj 0 = walkingAdjunctionIdentity .minus := by
    apply walkingAdjunctionOrdinalCard_injective .minus .minus
    exact hc.trans rfl
  exact (walkingAdjunctionConst_of_card_one H hcards).trans
    (congrArg (fun A => (Functor.const (Fin (n + 1))).obj A) ho)

/-- 概要：非退化なminus自己Homの正の実鎖で二番目の頂点が一点なら、次数は1。
方針：その先の実対象も一点なので、二番目の実辺は同型となることを排除する。
規約：n+1が元の実次数。使われ方：Riehl–Verity §4.2の余単位の場合の次数の検収。 -/
lemma walkingAdjunctionMinusChain_dimension_zero_of_second_card_one {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .minus) (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus .minus).nonDegenerate (n + 1))
    (hc : walkingAdjunctionOrdinalCard .minus .minus (H.obj 1) = 1) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    have hnext := walkingAdjunctionMinusHom_target_card_one (H.map' 1 2) hc
    have hi := walkingAdjunctionHom_isIso_of_card_one (H.map' 1 2) hc hnext
    exact False.elim
      ((walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd 1 hi)

end SerrePositivity.InfinityCategories.HA.Monads

module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalMapVariation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpoints
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIsoDegeneracy

/-!
概要：実辺の像の個数から全鎖の幅の有限順序表示を作り、非退化な原子の次元を押さえる。
方針：変化量0の実射は同型と示し、非退化な実辺の正値を全隣接辺で足す。
規約：原典の文字列の幅との全比較とfiltrationの全構成は別に行う。
使われ方：Riehl–Verity Proposition 4.2.15の実filtrationの順序づけ、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実非退化原子の有限の境界。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実辺の変化量0は元の四Homでの同型性と同値。
方針：個数と全点の値で恒等射へ戻し、逆向きは同型の実像の全射性を使う。
規約：元の実射の同型性。使われ方：Riehl–Verity §4.2の非退化な実辺の正値。 -/
lemma walkingAdjunctionMapVariation_zero_iff_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    ordinalMapVariation (walkingAdjunctionOrderHom f) = 0 ↔ IsIso f := by
  constructor
  · intro h
    have hab : A = B := walkingAdjunctionOrdinalCard_injective X Y
      (ordinalMapVariation_zero_card (walkingAdjunctionOrderHom f) h)
    subst B
    have hf : f = 𝟙 A := by
      apply walkingAdjunctionOrderHom_injective
      apply OrderHom.ext
      funext i
      apply Fin.ext
      rw [walkingAdjunctionOrderHom_id]
      exact ordinalMapVariation_zero_val (walkingAdjunctionOrderHom f) h i
    rw [hf]
    infer_instance
  · intro h
    have := h
    have hc := walkingAdjunctionCard_eq_of_isIso f
    have hr := (ordinalImageCard_eq_target_iff (walkingAdjunctionOrderHom f)).mpr
      (walkingAdjunctionOrderIsoOfIsIso f).surjective
    unfold ordinalMapVariation
    rw [hr, hc]
    omega

/-- 概要：非同型な実辺の変化量は正。
方針：変化量0の実同型の判定の逆を使う。
規約：元のHomの非同型性。使われ方：Riehl–Verity §4.2の次元の幅による境界。 -/
lemma walkingAdjunctionMapVariation_pos_of_not_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) (h : ¬ IsIso f) :
    0 < ordinalMapVariation (walkingAdjunctionOrderHom f) := by
  by_contra hn
  have hz : ordinalMapVariation (walkingAdjunctionOrderHom f) = 0 := by omega
  exact h ((walkingAdjunctionMapVariation_zero_iff_isIso f).mp hz)

/-- 概要：実全鎖の両端の個数と全隣接辺の変化量から定まる有限順序の幅。
方針：両端の補正を除いた個数に全実辺の変化量を足す。
規約：文字列の幅との全比較は未完。使われ方：Riehl–Verity Proposition 4.2.15の実表示。 -/
def walkingAdjunctionOrdinalWidth {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) : ℕ :=
  walkingAdjunctionOrdinalCard X Y (H.obj 0) +
    walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) -
      (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y) +
    ∑ j : Fin n, ordinalMapVariation
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))

/-- 概要：原子の有限順序の幅は1と全隣接辺の変化量の和。
方針：原子の両端の個数を幅の式へ適用する。
規約：全次数の実原子。使われ方：Riehl–Verity Proposition 4.2.15の実次元の境界。 -/
lemma walkingAdjunctionOrdinalWidth_atomic {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalWidth H = 1 + ∑ j : Fin n, ordinalMapVariation
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j)))) := by
  have hc := walkingAdjunctionAtomic_endpoint_cards H ha
  have hb : walkingAdjunctionOrdinalCard X Y (H.obj 0) +
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y) = 1 := by
    rw [hc.1, hc.2]
    omega
  unfold walkingAdjunctionOrdinalWidth
  rw [hb]

/-- 概要：非退化な実原子の次元は有限順序の幅より小さい。
方針：全隣接実辺が非同型なので各変化量は1以上であり、その有限和を使う。
規約：長さ0も含む元のnerveの非退化性。使われ方：Riehl–Verity Proposition 4.2.15の実境界。 -/
lemma walkingAdjunctionOrdinalWidth_dimension_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n) :
    n < walkingAdjunctionOrdinalWidth H := by
  rw [walkingAdjunctionOrdinalWidth_atomic H ha]
  cases n with
  | zero => simp
  | succ n =>
    have hno := (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd
    have hs : n + 1 ≤ ∑ j : Fin (n + 1), ordinalMapVariation
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j)))) := by
      calc
        n + 1 = ∑ _j : Fin (n + 1), (1 : ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j _ => Nat.succ_le_iff.mpr
          (walkingAdjunctionMapVariation_pos_of_not_isIso _ (hno j)))
    omega

end SerrePositivity.InfinityCategories.HA.Monads

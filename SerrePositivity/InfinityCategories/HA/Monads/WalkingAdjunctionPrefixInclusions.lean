module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionResidualFunctor

/-!
概要：実水平分解の左因子を先頭区間として全体へ入れ、その全射の可換性を証明する。
方針：全水平合成の共通表示と、順序和・端点共有の左の包含を使う。
規約：対象だけでなく全射を保持する。使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの因子の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：異なる個数で表示した射の異種等式を、同じ値の実点で評価する。
方針：個数と射を同一視する。規約：点の値の等式を明示する。
使われ方：Riehl–Verity Proposition 3.1.10 の射の照合。 -/
lemma ordinalOrderHom_heq_val {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d) (h : HEq f g)
    (i : Fin a) (j : Fin c) (hij : i.val = j.val) : (f i).val = (g j).val := by
  subst c
  subst d
  have hfg : f = g := eq_of_heq h
  subst g
  have hij' : i = j := Fin.ext hij
  subst j
  rfl

/-- 概要：左因子の点の個数は水平合成の点の個数以下。
方針：plusは順序和、minusは端点共有の個数の法則を使う。
規約：全八合成を含む。使われ方：Riehl–Verity Proposition 3.1.10 の先頭区間。 -/
lemma walkingAdjunctionHorizontal_prefix_card_le (X M Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom M Y) :
    walkingAdjunctionOrdinalCard X M A ≤
      walkingAdjunctionOrdinalCard X Y ((walkingAdjunctionHorizontal X M Y).obj (A, B)) := by
  cases M
  · have hs := walkingAdjunctionOrdinalCard_comp_plus X Y A B
    omega
  · have hs := walkingAdjunctionOrdinalCard_comp_minus X Y A B
    have hl := walkingAdjunctionIncoming_card X A
    omega

/-- 概要：水平合成の全射を左の先頭区間で評価すると左因子の全射へ戻る。
方針：二つの共通表示の左の包含を照合し、係数と区間表示を輸送する。
規約：空の因子と共有点を含む。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionHorizontal_prefix_val (X M Y : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X M} {B B' : walkingAdjunctionHom M Y}
    (f : A ⟶ A') (g : B ⟶ B') (i : Fin (walkingAdjunctionOrdinalCard X M A)) :
    (walkingAdjunctionOrderHom
      ((walkingAdjunctionHorizontal X M Y).map (X := (A, B)) (Y := (A', B')) (f, g))
        (Fin.castLE (walkingAdjunctionHorizontal_prefix_card_le X M Y A B) i)).val =
      (walkingAdjunctionOrderHom f i).val := by
  cases M
  · have hv := ordinalOrderHom_heq_val
      (walkingAdjunctionOrdinalCard_comp_plus X Y A B)
      (walkingAdjunctionOrdinalCard_comp_plus X Y A' B')
      _ _ (walkingAdjunctionOrderHom_comp_plus X Y f g)
      (Fin.castLE (walkingAdjunctionHorizontal_prefix_card_le X .plus Y A B) i)
      (i.castAdd (walkingAdjunctionOrdinalCard .plus Y B)) rfl
    rw [ordinalAppend_castAdd] at hv
    exact hv
  · let i' : Fin (walkingAdjunctionIncomingDim X A + 1) := ⟨i.val, by
      rw [← walkingAdjunctionIncoming_card X A]
      exact i.isLt⟩
    have hv := ordinalOrderHom_heq_val
      (walkingAdjunctionOrdinalCard_comp_minus X Y A B)
      (walkingAdjunctionOrdinalCard_comp_minus X Y A' B')
      _ _ (walkingAdjunctionOrderHom_comp_minus X Y f g)
      (Fin.castLE (walkingAdjunctionHorizontal_prefix_card_le X .minus Y A B) i)
      (⟨i'.val, by have := i'.isLt; omega⟩) rfl
    have hl := ordinalGlue_val_left
      (walkingAdjunctionIncomingMap f) (walkingAdjunctionOutgoingMap g) i'
    have hi := ordinalOrderHom_heq_val (walkingAdjunctionIncoming_card X A).symm
      (walkingAdjunctionIncoming_card X A').symm _ _ (walkingAdjunctionIncomingMap_heq f) i' i rfl
    exact hv.trans (hl.trans hi)

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：実水平分解の左因子の個数は全体の個数以下。
方針：実合成の個数の比較を指定単体Hへ移す。
規約：合成の等式を使う。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.prefix_card_le (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard X a.middle (a.left.obj i) ≤
      walkingAdjunctionOrdinalCard X Y (H.obj i) := by
  rw [← CategoryTheory.Functor.congr_obj a.fac i]
  exact walkingAdjunctionHorizontal_prefix_card_le X a.middle Y (a.left.obj i) (a.right.obj i)

/-- 概要：実水平分解の左因子の先頭区間への包含。
方針：元の点の値を変えない包含を使う。規約：同じHに入れる。
使われ方：Riehl–Verity Proposition 3.1.10 の残りの射の照合。 -/
def WalkingAdjunctionFactorization.prefixInclusion (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard X a.middle (a.left.obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i)) :=
  (Fin.castLEOrderEmb (a.prefix_card_le i)).toOrderHom

/-- 概要：実水平分解の左因子の全射は、先頭区間の包含と可換。
方針：元の八合成の左の包含の計算を同じHへ戻す。
規約：全ての射の正方形。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.prefix_square (a : WalkingAdjunctionFactorization H)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (a.prefixInclusion j).comp (walkingAdjunctionOrderHom (a.left.map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp (a.prefixInclusion i) := by
  rcases a with ⟨M, L, R, h⟩
  subst H
  apply OrderHom.ext
  funext x
  apply Fin.ext
  exact (walkingAdjunctionHorizontal_prefix_val X M Y (L.map f) (R.map f) x).symm

end SerrePositivity.InfinityCategories.HA.Monads

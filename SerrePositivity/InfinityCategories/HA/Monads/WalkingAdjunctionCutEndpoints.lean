module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIntervalLaws

/-!
概要：plusの切れ目を終頂点、minusの共有点を始頂点から実際に構成する。
方針：元の全単体の射の共通表示と逆向きの区間表示で各頂点へ運ぶ。
規約：自然性を構成し、端点での値と元の切れ目の両往復を保持する。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の切れ目の表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)

/-- 概要：終頂点の実切れ目から全単体上のplusの切れ目を作る。
方針：終頂点への各射の逆向きの区間表示で引き戻す。
規約：全射の自然性を合成則から証明する。使われ方：Riehl–Verity §4.1。 -/
def WalkingAdjunctionPlusCut.ofLast
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1)) :
    WalkingAdjunctionPlusCut H where
  value i := ordinalIntervalMap (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i)))) t
  naturality {i j} hij := by
    change ((ordinalIntervalMap (walkingAdjunctionOrderHom (H.map (homOfLE hij)))).comp
      (ordinalIntervalMap (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.le_last j)))))) t = _
    rw [← ordinalIntervalMap_comp, ← walkingAdjunctionOrderHom_comp, ← H.map_comp]
    rfl

/-- 概要：構成したplusの切れ目の終頂点の値は指定した値。
方針：終頂点の恒等射の表示を使う。規約：端点を含む全切れ目。
使われ方：Riehl–Verity §4.1の表示の往復。 -/
lemma WalkingAdjunctionPlusCut.ofLast_value_last
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1)) :
    (WalkingAdjunctionPlusCut.ofLast H t).value (Fin.last n) = t := by
  change ordinalIntervalMap (walkingAdjunctionOrderHom
    (H.map (homOfLE (Fin.le_last (Fin.last n))))) t = t
  have he : homOfLE (Fin.le_last (Fin.last n)) = 𝟙 (Fin.last n) := Subsingleton.elim _ _
  rw [he, H.map_id, walkingAdjunctionOrderHom_id, ordinalIntervalMap_id]
  rfl

/-- 概要：plusの切れ目を終頂点から作り直すと同じ実データ。
方針：終頂点での単射性と評価の法則を使う。規約：自然性も含む。
使われ方：Riehl–Verity §4.1の全切れ目の表示。 -/
lemma WalkingAdjunctionPlusCut.ofLast_roundtrip (a : WalkingAdjunctionPlusCut H) :
    WalkingAdjunctionPlusCut.ofLast H (a.value (Fin.last n)) = a :=
  WalkingAdjunctionPlusCut.last_injective (WalkingAdjunctionPlusCut.ofLast_value_last H _)

/-- 概要：plusの切れ目と終頂点の有限切れ目の実全単射。
方針：評価と構成した逆写像の両往復を使う。規約：全切れ目を含む。
使われ方：Riehl–Verity §4.1の原子的な分解の比較。 -/
def WalkingAdjunctionPlusCut.lastEquiv : WalkingAdjunctionPlusCut H ≃
    Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1) where
  toFun a := a.value (Fin.last n)
  invFun := WalkingAdjunctionPlusCut.ofLast H
  left_inv := WalkingAdjunctionPlusCut.ofLast_roundtrip H
  right_inv := WalkingAdjunctionPlusCut.ofLast_value_last H

/-- 概要：始頂点の実点から全単体上のminusの共有点を作る。
方針：始頂点からの各射の共通表示で運ぶ。
規約：全射の自然性を合成則から証明する。使われ方：Riehl–Verity §4.1。 -/
def WalkingAdjunctionMinusCut.ofFirst
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0))) : WalkingAdjunctionMinusCut H where
  value i := walkingAdjunctionOrderHom (H.map (homOfLE (Fin.zero_le i))) t
  naturality {i j} hij := by
    change ((walkingAdjunctionOrderHom (H.map (homOfLE hij))).comp
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.zero_le i))))) t = _
    rw [← walkingAdjunctionOrderHom_comp, ← H.map_comp]
    rfl

/-- 概要：構成したminusの共有点の始頂点の値は指定した値。
方針：始頂点の恒等射の表示を使う。規約：全点。
使われ方：Riehl–Verity §4.1の表示の往復。 -/
lemma WalkingAdjunctionMinusCut.ofFirst_value_zero
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0))) :
    (WalkingAdjunctionMinusCut.ofFirst H t).value 0 = t := by
  change walkingAdjunctionOrderHom (H.map (homOfLE (Fin.zero_le (0 : Fin (n + 1))))) t = t
  have he : homOfLE (Fin.zero_le (0 : Fin (n + 1))) = 𝟙 (0 : Fin (n + 1)) := Subsingleton.elim _ _
  rw [he, H.map_id, walkingAdjunctionOrderHom_id]
  rfl

/-- 概要：minusの共有点を始頂点から作り直すと同じ実データ。
方針：始頂点での単射性と評価の法則を使う。規約：自然性も含む。
使われ方：Riehl–Verity §4.1の全共有点の表示。 -/
lemma WalkingAdjunctionMinusCut.ofFirst_roundtrip (a : WalkingAdjunctionMinusCut H) :
    WalkingAdjunctionMinusCut.ofFirst H (a.value 0) = a :=
  WalkingAdjunctionMinusCut.first_injective (WalkingAdjunctionMinusCut.ofFirst_value_zero H _)

/-- 概要：minusの共有点と始頂点の有限点の実全単射。
方針：評価と構成した逆写像の両往復を使う。規約：空の場合も含む。
使われ方：Riehl–Verity §4.1の原子的な分解の比較。 -/
def WalkingAdjunctionMinusCut.firstEquiv : WalkingAdjunctionMinusCut H ≃
    Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0)) where
  toFun a := a.value 0
  invFun := WalkingAdjunctionMinusCut.ofFirst H
  left_inv := WalkingAdjunctionMinusCut.ofFirst_roundtrip H
  right_inv := WalkingAdjunctionMinusCut.ofFirst_value_zero H

end SerrePositivity.InfinityCategories.HA.Monads

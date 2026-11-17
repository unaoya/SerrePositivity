module

public import SerrePositivity.InfinityCategories.HA.Monads.IntervalInverseMapProfiles

/-!
概要：walking adjunctionの四Homの全射を共通の有限単調射の表示で照合する。
方針：既存のHom圏・区間表示を場合分けし、対象の重みと全射の照合をまとめる。
規約：射の表示から元の射の異種等式も回収する。新しい∞圏の仮定は置かない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：有限単調射の表示の点の個数。
方針：自己Homのplus側だけ空も許す。規約：既存の四表示の同じ個数。
使われ方：Riehl–Verity Remark 3.3.8 の全合成の係数移送。 -/
def walkingAdjunctionOrdinalCard : (X Y : WalkingAdjunctionPoint) → walkingAdjunctionHom X Y → ℕ
  | .plus, .plus, A => augmentedOrdinalCard A
  | .plus, .minus, A => A.obj.len + 1
  | .minus, .plus, A => A.obj.len + 1
  | .minus, .minus, A => augmentedOrdinalCard A.unop + 1

/-- 概要：四Homの全射の共通の有限単調射の表示。
方針：plus自己Homは元の射、minus自己Homは区間表示、混合Homは元の単体圏の射。
規約：全射を保持する。使われ方：HA Proposition 4.7.3.3 の全水平結合則。 -/
def walkingAdjunctionOrderHom {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    Fin (walkingAdjunctionOrdinalCard X Y A) →o Fin (walkingAdjunctionOrdinalCard X Y B) := by
  cases X <;> cases Y
  · exact augmentedOrderHom f
  · exact f.hom.toOrderHom
  · exact f.hom.toOrderHom
  · exact ordinalIntervalMap (augmentedOrderHom f.unop)

/-- 概要：minusに入るHomの区間の次元。
方針：最大元保存と区間表示を同じ添字で扱う。規約：点の個数は次元+1。
使われ方：Riehl–Verity Remark 3.3.8 の端点共有の係数。 -/
def walkingAdjunctionIncomingDim : (X : WalkingAdjunctionPoint) → walkingAdjunctionHom X .minus → ℕ
  | .plus, A => A.obj.len
  | .minus, A => augmentedOrdinalCard A.unop

/-- 概要：minusから出るHomの区間の次元。
方針：最小元保存と区間表示の次元を取る。規約：全て非空の区間。
使われ方：Riehl–Verity Remark 3.3.8 の端点共有の係数。 -/
def walkingAdjunctionOutgoingDim : (Y : WalkingAdjunctionPoint) → walkingAdjunctionHom .minus Y → ℕ
  | .plus, A => A.obj.len
  | .minus, A => augmentedOrdinalCard A.unop

/-- 概要：minusに入るHomの射の非空区間の表示。
方針：既存の二つの表示を使う。規約：次元+1の型を明示する。
使われ方：HA Proposition 4.7.3.3 の端点共有の全射。 -/
def walkingAdjunctionIncomingMap {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B) :
    Fin (walkingAdjunctionIncomingDim X A + 1) →o Fin (walkingAdjunctionIncomingDim X B + 1) := by
  cases X
  · exact f.hom.toOrderHom
  · exact ordinalIntervalMap (augmentedOrderHom f.unop)

/-- 概要：minusから出るHomの射の非空区間の表示。
方針：既存の最小元保存と区間表示を使う。規約：次元を区別する。
使われ方：HA Proposition 4.7.3.3 の端点共有の全射。 -/
def walkingAdjunctionOutgoingMap {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) :
    Fin (walkingAdjunctionOutgoingDim Y A + 1) →o Fin (walkingAdjunctionOutgoingDim Y B + 1) := by
  cases Y
  · exact f.hom.toOrderHom
  · exact ordinalIntervalMap (augmentedOrderHom f.unop)

/-- 概要：minusを終点とする表示の点の個数の補正。
方針：plusは0、minusは1。規約：既存の重みと個数を合わせるだけ。
使われ方：Riehl–Verity Remark 3.3.8 の対象の全結合則の係数。 -/
def walkingAdjunctionTargetCorrection : WalkingAdjunctionPoint → ℕ
  | .plus => 0
  | .minus => 1

/-- 概要：表示の個数は既存の重みと終点の補正で決まる。
方針：四Homを場合分けする。規約：同じ対象の個数。
使われ方：HA Proposition 4.7.3.3 の水平結合則の型の輸送。 -/
lemma walkingAdjunctionOrdinalCard_weight (X Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionOrdinalCard X Y A =
      walkingAdjunctionWeight X Y A + walkingAdjunctionTargetCorrection Y := by
  cases X <;> cases Y <;> rfl

/-- 概要：入る区間の次元は既存の重み。
方針：二つのHomの定義。規約：同じminus終点。
使われ方：Riehl–Verity Remark 3.3.8 の貼り合わせの対象の計算。 -/
lemma walkingAdjunctionIncomingDim_weight (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) :
    walkingAdjunctionIncomingDim X A = walkingAdjunctionWeight X .minus A := by
  cases X <;> rfl

/-- 概要：入る区間の個数は次元+1。
方針：二つの既存の表示の定義。規約：空の区間にしない。
使われ方：HA Proposition 4.7.3.3 の係数移送。 -/
lemma walkingAdjunctionIncoming_card (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) :
    walkingAdjunctionOrdinalCard X .minus A = walkingAdjunctionIncomingDim X A + 1 := by
  cases X <;> rfl

/-- 概要：出る区間の個数も次元+1。
方針：最小元保存と区間表示の定義。規約：同じminus始点。
使われ方：HA Proposition 4.7.3.3 の係数移送。 -/
lemma walkingAdjunctionOutgoing_card (Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom .minus Y) :
    walkingAdjunctionOrdinalCard .minus Y A = walkingAdjunctionOutgoingDim Y A + 1 := by
  cases Y <;> rfl

/-- 概要：入る射の表示は共通表示と同じ全射。
方針：二つのHomを場合分けする。規約：型の違いはHEqで保持。
使われ方：Riehl–Verity Remark 3.3.8 の端点共有への移送。 -/
lemma walkingAdjunctionIncomingMap_heq {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B) :
    HEq (walkingAdjunctionIncomingMap (X := X) f)
      (walkingAdjunctionOrderHom (X := X) (Y := .minus) f) := by
  cases X <;> rfl

/-- 概要：出る射の表示も共通表示と同じ全射。
方針：二つのHomを場合分けする。規約：元の射を変えない。
使われ方：Riehl–Verity Remark 3.3.8 の端点共有への移送。 -/
lemma walkingAdjunctionOutgoingMap_heq {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) :
    HEq (walkingAdjunctionOutgoingMap (Y := Y) f)
      (walkingAdjunctionOrderHom (X := .minus) (Y := Y) f) := by
  cases Y <;> rfl

/-- 概要：共通表示の点の個数は元の対象を区別する。
方針：既存の重みの単射性と個数の補正を使う。
規約：同じ二つの端点。使われ方：HA Proposition 4.7.3.3 の対象の照合。 -/
lemma walkingAdjunctionOrdinalCard_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionOrdinalCard X Y) := by
  intro A B h
  apply walkingAdjunctionWeight_injective X Y
  have ha := walkingAdjunctionOrdinalCard_weight X Y A
  have hb := walkingAdjunctionOrdinalCard_weight X Y B
  omega

/-- 概要：plusを挟む合成の個数は二つの個数の和。
方針：既存の合成の重みの加法則と個数の補正を使う。
規約：同じ実双関手。使われ方：Riehl–Verity Remark 3.3.8 の順序和の係数。 -/
lemma walkingAdjunctionOrdinalCard_comp_plus (X Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .plus) (B : walkingAdjunctionHom .plus Z) :
    walkingAdjunctionOrdinalCard X Z ((walkingAdjunctionHorizontal X .plus Z).obj (A, B)) =
      walkingAdjunctionOrdinalCard X .plus A + walkingAdjunctionOrdinalCard .plus Z B := by
  have hs := walkingAdjunctionHorizontal_weight X .plus Z A B
  have ho := walkingAdjunctionOrdinalCard_weight X Z
    ((walkingAdjunctionHorizontal X .plus Z).obj (A, B))
  have ha := walkingAdjunctionOrdinalCard_weight X .plus A
  have hb := walkingAdjunctionOrdinalCard_weight .plus Z B
  change walkingAdjunctionOrdinalCard X .plus A = walkingAdjunctionWeight X .plus A + 0 at ha
  omega

/-- 概要：minusを挟む合成の個数は二つの区間の次元の和+1。
方針：重みの加法則と入出の区間の個数を合わせる。
規約：既存の区間の端点共有の対象。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma walkingAdjunctionOrdinalCard_comp_minus (X Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) (B : walkingAdjunctionHom .minus Z) :
    walkingAdjunctionOrdinalCard X Z ((walkingAdjunctionHorizontal X .minus Z).obj (A, B)) =
      walkingAdjunctionIncomingDim X A + walkingAdjunctionOutgoingDim Z B + 1 := by
  have hs := walkingAdjunctionHorizontal_weight X .minus Z A B
  have ho := walkingAdjunctionOrdinalCard_weight X Z
    ((walkingAdjunctionHorizontal X .minus Z).obj (A, B))
  have ha := walkingAdjunctionIncomingDim_weight X A
  have hb := walkingAdjunctionOutgoing_card Z B
  have hb' := walkingAdjunctionOrdinalCard_weight .minus Z B
  omega

/-- 概要：共通表示の全射の異種等式から元の射を回収する。
方針：対象を戻し、各Homの既存の忠実な表示の単射性を使う。
規約：同じ端点のHom内。使われ方：HA Proposition 4.7.3.3 の全関手の結合則の回収。 -/
lemma walkingAdjunctionOrderHom_hext {X Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom X Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq (walkingAdjunctionOrderHom (X := X) (Y := Y) f)
      (walkingAdjunctionOrderHom (X := X) (Y := Y) g)) : HEq f g := by
  subst A'
  subst B'
  apply heq_of_eq
  cases X <;> cases Y
  · exact (augmentedOrderHomEquiv A B).injective (eq_of_heq h)
  · apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    exact eq_of_heq h
  · apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    exact eq_of_heq h
  · apply Quiver.Hom.unop_inj
    apply (augmentedOrderHomEquiv B.unop A.unop).injective
    apply (ordinalIntervalHomEquiv _ _).injective
    apply Subtype.ext
    exact eq_of_heq h

/-- 概要：plusを挟む四つの全水平合成の全射は順序和。
方針：検証済みの四比較を同じ型でまとめる。
規約：全ての端点と射。使われ方：HA Proposition 4.7.3.3 の全結合則。 -/
lemma walkingAdjunctionOrderHom_comp_plus (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .plus} {B B' : walkingAdjunctionHom .plus Z}
    (f : A ⟶ A') (g : B ⟶ B') :
    HEq (walkingAdjunctionOrderHom (X := X) (Y := Z)
        ((walkingAdjunctionHorizontal X .plus Z).map (X := (A, B)) (Y := (A', B')) (f, g)))
      (ordinalAppend (walkingAdjunctionOrderHom (X := X) (Y := .plus) f)
        (walkingAdjunctionOrderHom (X := .plus) (Y := Z) g)) := by
  cases X <;> cases Z
  · exact augmentedOrderHom_tensor f g
  · exact topOrdinalAction_map_heq f g
  · exact bottomOrdinalAction_map_heq f g
  · exact mixedBottomTopInterval_map_heq f g

/-- 概要：minusを挟む四つの全水平合成の全射は端点共有。
方針：混合合成・二作用・反対の順序和の検証済みの射の比較をまとめる。
規約：元の全合成を比較する。使われ方：HA Proposition 4.7.3.3 の全結合則。 -/
lemma walkingAdjunctionOrderHom_comp_minus (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .minus} {B B' : walkingAdjunctionHom .minus Z}
    (f : A ⟶ A') (g : B ⟶ B') :
    HEq (walkingAdjunctionOrderHom (X := X) (Y := Z)
        ((walkingAdjunctionHorizontal X .minus Z).map (X := (A, B)) (Y := (A', B')) (f, g)))
      (ordinalGlue (walkingAdjunctionIncomingMap (X := X) f)
        (walkingAdjunctionOutgoingMap (Y := Z) g)) := by
  cases X <;> cases Z
  · exact mixedTopBottomOrdinal_map_heq f g
  · exact topOppositeOrdinalAction_map_heq f g
  · exact bottomOppositeOrdinalAction_map_heq f g
  · exact augmentedInterval_tensor_heq f.unop g.unop

end SerrePositivity.InfinityCategories.HA.Monads

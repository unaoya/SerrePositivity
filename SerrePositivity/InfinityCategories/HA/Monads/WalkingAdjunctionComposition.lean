module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalLaws
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingMonadLaws

/-!
概要：walking adjunctionの二対象・四つのHom圏・八つの水平合成を同時に指定する。
方針：増大単体圏・端点保存の圏の実双関手をまとめ、対象の法則を個数で証明する。
規約：合成の引数は先に使う射、後に使う射の順。Riehl–Verityの水平反対を使い、
plusの自己Homの積をNativeMonadの順序和と一致させる。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8。
Kerodon Remark 6.2.1.4（Tag 02EN）。この段階では豊穣圏のinstanceを宣言しない。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：walking adjunctionの二つの対象。
方針：plusをモナドの底とする。規約：水平反対の向き。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8。 -/
inductive WalkingAdjunctionPoint where
  /-- モナドが作用する側。 -/
  | plus
  /-- 自由対象が入る側。 -/
  | minus
  deriving DecidableEq

/-- 概要：二つの自己Homと二つの混合Homの実圏の台。
方針：増大単体圏・その反対・最大元保存・最小元保存を使う。
規約：plusからminusが左随伴の生成射。使われ方：Riehl–Verity Remark 3.3.8。 -/
def walkingAdjunctionHom : WalkingAdjunctionPoint → WalkingAdjunctionPoint → Type
  | .plus, .plus => AugmentedSimplexCategory
  | .plus, .minus => TopSimplexCategory
  | .minus, .plus => BottomSimplexCategory
  | .minus, .minus => AugmentedSimplexCategoryᵒᵖ

/-- 概要：四つのHomはそれぞれ構成済みの実圏。
方針：対象を場合分けする。規約：Homの圏構造を引数の仮定にしない。
使われ方：Riehl–Verity Remark 3.3.8 の全単体のnerve。 -/
instance walkingAdjunctionHom_category (X Y : WalkingAdjunctionPoint) :
    Category (walkingAdjunctionHom X Y) := by
  cases X <;> cases Y <;> dsimp [walkingAdjunctionHom] <;> infer_instance

/-- 概要：八つの実双関手による全水平合成のデータ。
方針：自己Homは順序和、混合Homは端点保存の作用・区間表示を使う。
規約：対象と射の双方を保持する。使われ方：HA Proposition 4.7.3.3 の合成。 -/
def walkingAdjunctionHorizontal : (X Y Z : WalkingAdjunctionPoint) →
    walkingAdjunctionHom X Y × walkingAdjunctionHom Y Z ⥤ walkingAdjunctionHom X Z
  | .plus, .plus, .plus => tensor AugmentedSimplexCategory
  | .plus, .plus, .minus => topOrdinalAction
  | .plus, .minus, .plus => mixedTopBottomOrdinal
  | .plus, .minus, .minus => topOppositeOrdinalAction
  | .minus, .plus, .plus => bottomOrdinalAction
  | .minus, .plus, .minus => mixedBottomTopOrdinal
  | .minus, .minus, .plus => bottomOppositeOrdinalAction
  | .minus, .minus, .minus =>
      (prodOpEquiv (C := AugmentedSimplexCategory) (D := AugmentedSimplexCategory)).inverse ⋙
        (tensor AugmentedSimplexCategory).op

/-- 概要：二対象の水平合成の単位の対象。
方針：それぞれ空順序集合を取る。規約：自己Hom内の対象。
使われ方：HA §4.7.2、Riehl–Verity Remark 3.3.8。 -/
def walkingAdjunctionIdentity : (X : WalkingAdjunctionPoint) → walkingAdjunctionHom X X
  | .plus => WithInitial.star
  | .minus => op WithInitial.star

/-- 概要：四つのHomの対象を共通の非負整数の重みで表す。
方針：最小元保存側だけ次元に1を加える。規約：左随伴の生成射の重みは0。
使われ方：Riehl–Verity Remark 3.3.8 の全対象の結合則。 -/
def walkingAdjunctionWeight : (X Y : WalkingAdjunctionPoint) → walkingAdjunctionHom X Y → ℕ
  | .plus, .plus, f => augmentedOrdinalCard f
  | .plus, .minus, f => f.obj.len
  | .minus, .plus, f => f.obj.len + 1
  | .minus, .minus, f => augmentedOrdinalCard f.unop

/-- 概要：各Homの重みは対象を区別する。
方針：増大単体圏の個数と単体圏の次元の単射性を使う。
規約：同じ始点・終点の対象同士。使われ方：Riehl–Verity Remark 3.3.8 の骨格。 -/
lemma walkingAdjunctionWeight_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionWeight X Y) := by
  cases X <;> cases Y
  · exact augmentedOrdinalCard_injective
  · intro f g h
    apply WideSubcategory.ext
    exact SimplexCategory.ext h
  · intro f g h
    apply WideSubcategory.ext
    apply SimplexCategory.ext
    exact Nat.add_right_cancel h
  · intro f g h
    apply unop_injective
    exact augmentedOrdinalCard_injective h

/-- 概要：増大単体圏の順序和は点の個数を加える。
方針：空を場合分けする。規約：両因子とも空も許す。
使われ方：HA §4.7.2 の水平合成の対象計算。 -/
lemma augmentedOrdinalCard_tensor (X Y : AugmentedSimplexCategory) :
    augmentedOrdinalCard (X ⊗ Y) = augmentedOrdinalCard X + augmentedOrdinalCard Y := by
  change augmentedOrdinalCard (AugmentedSimplexCategory.tensorObj X Y) = _
  cases X <;> cases Y <;>
    simp only [AugmentedSimplexCategory.tensorObj,
      AugmentedSimplexCategory.tensorObjOf, augmentedOrdinalCard] <;> omega

/-- 概要：最大元保存の左水平合成の次元。
方針：空の作用と非空の順序和を分ける。
規約：同じ端点保存の圏。使われ方：Riehl–Verity Remark 3.3.8 の合成の対象。 -/
lemma topOrdinalAction_len (a : AugmentedSimplexCategory) (X : TopSimplexCategory) :
    (topOrdinalAction.obj (a, X)).obj.len = augmentedOrdinalCard a + X.obj.len := by
  cases a with
  | star => change X.obj.len = 0 + X.obj.len; omega
  | of a =>
    change a.len + X.obj.len + 1 = a.len + 1 + X.obj.len
    omega

/-- 概要：最小元保存の右水平合成の次元。
方針：空の作用と非空の順序和を分ける。規約：元の変数の順序。
使われ方：Riehl–Verity Remark 3.3.8 の合成の対象。 -/
lemma bottomOrdinalAction_len (X : BottomSimplexCategory) (a : AugmentedSimplexCategory) :
    (bottomOrdinalAction.obj (X, a)).obj.len = X.obj.len + augmentedOrdinalCard a := by
  cases a with
  | star => change X.obj.len = X.obj.len + 0; omega
  | of a =>
    change X.obj.len + a.len + 1 = X.obj.len + (a.len + 1)
    omega

/-- 概要：双対側の最小元保存の左水平合成の次元。
方針：Galois双対が対象を変えないことを使う。
規約：増大単体圏の反対。使われ方：Riehl–Verity Remark 3.3.8 の合成の対象。 -/
lemma bottomOppositeOrdinalAction_len (a : AugmentedSimplexCategoryᵒᵖ)
    (X : BottomSimplexCategory) :
    (bottomOppositeOrdinalAction.obj (a, X)).obj.len =
      augmentedOrdinalCard a.unop + X.obj.len := by
  exact topOrdinalAction_len a.unop ⟨X.obj⟩

/-- 概要：双対側の最大元保存の右水平合成の次元。
方針：Galois双対と右作用の次元則を使う。規約：元の二つの変数。
使われ方：Riehl–Verity Remark 3.3.8 の合成の対象。 -/
lemma topOppositeOrdinalAction_len (X : TopSimplexCategory)
    (a : AugmentedSimplexCategoryᵒᵖ) :
    (topOppositeOrdinalAction.obj (X, a)).obj.len =
      X.obj.len + augmentedOrdinalCard a.unop := by
  exact bottomOrdinalAction_len ⟨X.obj⟩ a.unop

/-- 概要：八つの水平合成は同じ重みの加法を持つ。
方針：実装済みの八双関手の対象計算を照合する。
規約：全組合せを量化する。使われ方：HA Proposition 4.7.3.3 の合成の骨格。 -/
lemma walkingAdjunctionHorizontal_weight (X Y Z : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom X Y) (g : walkingAdjunctionHom Y Z) :
    walkingAdjunctionWeight X Z ((walkingAdjunctionHorizontal X Y Z).obj (f, g)) =
      walkingAdjunctionWeight X Y f + walkingAdjunctionWeight Y Z g := by
  cases X <;> cases Y <;> cases Z
  · exact augmentedOrdinalCard_tensor f g
  · exact topOrdinalAction_len f g
  · have h := mixedTopBottomOrdinal_card f g
    change augmentedOrdinalCard (mixedTopBottomOrdinal.obj (f, g)) =
      f.obj.len + (g.obj.len + 1)
    omega
  · exact topOppositeOrdinalAction_len f g
  · have h := bottomOrdinalAction_len f g
    change (bottomOrdinalAction.obj (f, g)).obj.len + 1 =
      (f.obj.len + 1) + augmentedOrdinalCard g
    omega
  · have h := mixedBottomTopOrdinal_card f g
    change augmentedOrdinalCard (mixedBottomTopOrdinal.obj (f, g)).unop =
      (f.obj.len + 1) + g.obj.len
    omega
  · have h := bottomOppositeOrdinalAction_len f g
    change (bottomOppositeOrdinalAction.obj (f, g)).obj.len + 1 =
      augmentedOrdinalCard f.unop + (g.obj.len + 1)
    omega
  · exact augmentedOrdinalCard_tensor f.unop g.unop

/-- 概要：両側の水平恒等射の重みは0。
方針：空順序集合の個数。規約：全二対象。
使われ方：Riehl–Verity Remark 3.3.8 の水平単位則。 -/
lemma walkingAdjunctionIdentity_weight (X : WalkingAdjunctionPoint) :
    walkingAdjunctionWeight X X (walkingAdjunctionIdentity X) = 0 := by
  cases X <;> rfl

/-- 概要：全水平合成の対象の結合則。
方針：重みの単射性と自然数の加法の結合則を使う。
規約：射の結合則は別に検収する。使われ方：HA Proposition 4.7.3.3 のwalking adjunction。 -/
lemma walkingAdjunctionHorizontal_obj_assoc (W X Y Z : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom W X) (g : walkingAdjunctionHom X Y)
    (h : walkingAdjunctionHom Y Z) :
    (walkingAdjunctionHorizontal W Y Z).obj
        ((walkingAdjunctionHorizontal W X Y).obj (f, g), h) =
      (walkingAdjunctionHorizontal W X Z).obj
        (f, (walkingAdjunctionHorizontal X Y Z).obj (g, h)) := by
  apply walkingAdjunctionWeight_injective
  simp only [walkingAdjunctionHorizontal_weight, Nat.add_assoc]

/-- 概要：全水平合成の対象の左単位則。
方針：単位の重みが0であることと重みの単射性を使う。
規約：同じ対象等式。使われ方：Riehl–Verity Remark 3.3.8 の水平単位。 -/
lemma walkingAdjunctionHorizontal_obj_id_left (X Y : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom X Y) :
    (walkingAdjunctionHorizontal X X Y).obj (walkingAdjunctionIdentity X, f) = f := by
  apply walkingAdjunctionWeight_injective
  simp only [walkingAdjunctionHorizontal_weight, walkingAdjunctionIdentity_weight, zero_add]

/-- 概要：全水平合成の対象の右単位則。
方針：単位の重みが0であることと重みの単射性を使う。
規約：射の単位則は別に照合する。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma walkingAdjunctionHorizontal_obj_id_right (X Y : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom X Y) :
    (walkingAdjunctionHorizontal X Y Y).obj (f, walkingAdjunctionIdentity Y) = f := by
  apply walkingAdjunctionWeight_injective
  simp only [walkingAdjunctionHorizontal_weight, walkingAdjunctionIdentity_weight, add_zero]

end SerrePositivity.InfinityCategories.HA.Monads

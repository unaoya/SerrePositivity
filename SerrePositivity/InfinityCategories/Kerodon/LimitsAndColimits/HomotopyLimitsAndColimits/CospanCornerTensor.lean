module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanTensorCorner
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：重みの相対境界とパラメーターの pushout-product の交換同型。
方針：二通りの pushout の間に両方向の射を作り、生成成分で逆関係と境界射との可換性を示す。
規約：係数の宇宙に合わせて AsSmall.{u} WalkingCospan を使う。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、一脚だけが fibration の図式の重みの制限の全境界の充填。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {W W' : AsSmall.{u} WalkingCospan ⥤ SSet.{u}}

local notation "R" => (AsSmall.up.obj WalkingCospan.right)
local notation "O" => (AsSmall.up.obj WalkingCospan.one)
local notation "rleg" => (AsSmall.up.map WalkingCospan.Hom.inr)
/-- 概要：中央の相対境界の pushout はパラメーターとの直積で保存される。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma tensorRightCornerPushout (j : W ⟶ W') (B : SSet.{u}) :
    IsPushout (W.map rleg ▷ B) (j.app R ▷ B)
      (pushout.inl (W.map rleg) (j.app R) ▷ B) (pushout.inr (W.map rleg) (j.app R) ▷ B) :=
  (IsPushout.of_hasPushout (W.map rleg) (j.app R)).map (tensorRight B)
/-- 概要：直積と重みの pushout を経由する二つの右成分の射は整合する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma corner_tensor_glue (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (W.map rleg ▷ B) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inr.app O ≫
        pushout.inl ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) =
      (j.app R ▷ B) ≫
        pushout.inr ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f
  have h : (W.map rleg ▷ B) ≫ P.inr.app O = P.inr.app R ≫ P.pt.map rleg :=
    P.inr.naturality rleg
  change (W.map rleg ▷ B) ≫ P.inr.app O ≫ pushout.inl (P.pt.map rleg) (P.ι.app R) =
    (j.app R ▷ B) ≫ pushout.inr (P.pt.map rleg) (P.ι.app R)
  rw [← Category.assoc, h, Category.assoc, pushout.condition, ← Category.assoc]
  have hi : P.inr.app R ≫ P.ι.app R = j.app R ▷ B :=
    NatTrans.congr_app P.inr_ι R
  rw [hi]
/-- 概要：相対境界の始域との直積から、重みの pushout-product の相対境界の始域への射。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
noncomputable def cornerTensorMap (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    pushout (W.map rleg) (j.app R) ⊗ B ⟶
      pushout ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) :=
  (tensorRightCornerPushout j B).desc
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inr.app O ≫ pushout.inl _ _)
    (pushout.inr _ _) (corner_tensor_glue j f)
/-- 概要：貼り合わせた直積の射を元の中央成分に制限すると中央の pushout の右包含になる。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorMap_inl (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (pushout.inl (W.map rleg) (j.app R) ▷ B) ≫ cornerTensorMap j f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inr.app O ≫ pushout.inl _ _ :=
  (tensorRightCornerPushout j B).inl_desc _ _ _
/-- 概要：貼り合わせた直積の射を延長後の右成分に制限すると右の包含になる。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorMap_inr (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (pushout.inr (W.map rleg) (j.app R) ▷ B) ≫ cornerTensorMap j f =
      pushout.inr _ _ :=
  (tensorRightCornerPushout j B).inr_desc _ _ _
/-- 概要：直積の貼り合わせは中央の境界射とパラメーターの射に整合する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorMap_square (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j) ▷ A) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inl.app O ≫ pushout.inl _ _ =
      (pushout (W.map rleg) (j.app R) ◁ f) ≫ cornerTensorMap j f := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)
  apply (tensorRightCornerPushout j A).hom_ext
  · change (pushout.inl (W.map rleg) (j.app R) ▷ A) ≫ k ▷ A ≫
      P.inl.app O ≫ pushout.inl _ _ = _
    have hk : pushout.inl (W.map rleg) (j.app R) ≫ k = j.app O := pushout.inl_desc _ _ _
    rw [← Category.assoc, ← comp_whiskerRight, hk]
    have hw : (j.app O ▷ A) ≫ P.inl.app O = (W.obj O ◁ f) ≫ P.inr.app O :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j f O).isPushout.w
    rw [← Category.assoc, hw, Category.assoc]
    conv_rhs => rw [← whisker_exchange_assoc, cornerTensorMap_inl]
  · change (pushout.inr (W.map rleg) (j.app R) ▷ A) ≫ k ▷ A ≫
      P.inl.app O ≫ pushout.inl _ _ = _
    have hk : pushout.inr (W.map rleg) (j.app R) ≫ k = W'.map rleg := pushout.inr_desc _ _ _
    rw [← Category.assoc, ← comp_whiskerRight, hk]
    have hn : (W'.map rleg ▷ A) ≫ P.inl.app O = P.inl.app R ≫ P.pt.map rleg :=
      P.inl.naturality rleg
    rw [← Category.assoc, hn, Category.assoc, pushout.condition, ← Category.assoc]
    have hi : P.inl.app R ≫ P.ι.app R = W'.obj R ◁ f :=
      NatTrans.congr_app P.inl_ι R
    rw [hi]
    conv_rhs => rw [← whisker_exchange_assoc, cornerTensorMap_inr]
/-- 概要：直積の貼り合わせの後で境界射を適用すると元の相対境界の直積になる。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorMap_fac (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    cornerTensorMap j f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap
        (Functor.whiskerLeft AsSmall.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j) ▷ B := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)
  apply (tensorRightCornerPushout j B).hom_ext
  · rw [← Category.assoc, cornerTensorMap_inl, Category.assoc]
    change P.inr.app O ≫ pushout.inl (P.pt.map rleg) (P.ι.app R) ≫
      pushout.desc (P.ι.app O) ((W' ⊗ (Functor.const _).obj B).map rleg) _ =
      (pushout.inl (W.map rleg) (j.app R) ▷ B) ≫ k ▷ B
    rw [pushout.inl_desc, ← comp_whiskerRight]
    have hi : P.inr.app O ≫ P.ι.app O = j.app O ▷ B := NatTrans.congr_app P.inr_ι O
    rw [hi]
    have hk : pushout.inl (W.map rleg) (j.app R) ≫ k = j.app O := pushout.inl_desc _ _ _
    exact congrArg (fun g => g ▷ B) hk.symm
  · rw [← Category.assoc, cornerTensorMap_inr]
    change pushout.inr (P.pt.map rleg) (P.ι.app R) ≫
      pushout.desc (P.ι.app O) ((W' ⊗ (Functor.const _).obj B).map rleg) _ =
      (pushout.inr (W.map rleg) (j.app R) ▷ B) ≫ k ▷ B
    rw [pushout.inr_desc, ← comp_whiskerRight]
    have hk : pushout.inr (W.map rleg) (j.app R) ≫ k = W'.map rleg := pushout.inr_desc _ _ _
    change W'.map rleg ▷ B = (pushout.inr (W.map rleg) (j.app R) ≫ k) ▷ B
    exact congrArg (fun g => g ▷ B) hk.symm
/-- 概要：中央の相対境界の射とパラメーターの射の pushout-product。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
noncomputable def cornerTensorProduct (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (curriedTensor SSet.{u}).PushoutObjObj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)) f :=
  Functor.PushoutObjObj.ofHasPushout _ _ _
/-- 概要：相対境界の pushout-product から、pushout-product の相対境界への比較射。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
noncomputable def cornerTensorComparison (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (cornerTensorProduct j f).pt ⟶
      pushout ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) :=
  (cornerTensorProduct j f).isPushout.desc
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inl.app O ≫ pushout.inl _ _)
    (cornerTensorMap j f) (cornerTensorMap_square j f)
/-- 概要：相対境界の pushout-product の可換性を元の中央成分で表示する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorProduct_w_inl (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (j.app O ▷ A) ≫ (cornerTensorProduct j f).inl =
      (W.obj O ◁ f) ≫ (pushout.inl (W.map rleg) (j.app R) ▷ B) ≫
        (cornerTensorProduct j f).inr := by
  let Q := cornerTensorProduct j f
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)
  have hk : pushout.inl (W.map rleg) (j.app R) ≫ k = j.app O := pushout.inl_desc _ _ _
  have hQ : (k ▷ A) ≫ Q.inl = (pushout (W.map rleg) (j.app R) ◁ f) ≫ Q.inr :=
    Q.isPushout.w
  calc
    _ = (pushout.inl (W.map rleg) (j.app R) ▷ A) ≫ (k ▷ A) ≫ Q.inl := by
      rw [← Category.assoc, ← comp_whiskerRight, hk]
    _ = _ := by rw [hQ, whisker_exchange_assoc]
/-- 概要：相対境界の pushout-product の可換性を延長後の右成分で表示する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorProduct_w_inr (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (W'.map rleg ▷ A) ≫ (cornerTensorProduct j f).inl =
      (W'.obj R ◁ f) ≫ (pushout.inr (W.map rleg) (j.app R) ▷ B) ≫
        (cornerTensorProduct j f).inr := by
  let Q := cornerTensorProduct j f
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)
  have hk : pushout.inr (W.map rleg) (j.app R) ≫ k = W'.map rleg := pushout.inr_desc _ _ _
  have hQ : (k ▷ A) ≫ Q.inl = (pushout (W.map rleg) (j.app R) ◁ f) ≫ Q.inr :=
    Q.isPushout.w
  calc
    _ = (pushout.inr (W.map rleg) (j.app R) ▷ A) ≫ (k ▷ A) ≫ Q.inl := by
      rw [← Category.assoc, ← comp_whiskerRight, hk]
    _ = _ := by rw [hQ, whisker_exchange_assoc]
/-- 概要：交換比較の逆射を中央の成分の pushout 上で構成する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
noncomputable def cornerTensorReverseBase (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.obj O ⟶ (cornerTensorProduct j f).pt :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j f O).isPushout.desc (cornerTensorProduct j f).inl
    ((pushout.inl (W.map rleg) (j.app R) ▷ B) ≫ (cornerTensorProduct j f).inr)
    (cornerTensorProduct_w_inl j f)
/-- 概要：逆射の中央成分は左の包含上で相対境界の pushout-product の左包含になる。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorReverseBase_inl (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inl.app O ≫ cornerTensorReverseBase j f =
      (cornerTensorProduct j f).inl := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j f O).isPushout.inl_desc _ _ _
/-- 概要：逆射の中央成分は右の包含上で元の中央の直積を経由する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorReverseBase_inr (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inr.app O ≫ cornerTensorReverseBase j f =
      (pushout.inl (W.map rleg) (j.app R) ▷ B) ≫ (cornerTensorProduct j f).inr :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j f O).isPushout.inr_desc _ _ _
/-- 概要：逆射の中央成分と右成分は元の右成分の pushout 上で整合する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorReverse_glue (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg ≫ cornerTensorReverseBase j f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R ≫ (pushout.inr (W.map rleg) (j.app R) ▷ B) ≫
        (cornerTensorProduct j f).inr := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j f R).isPushout.hom_ext
  · have hn : P.inl.app R ≫ P.pt.map rleg = (W'.map rleg ▷ A) ≫ P.inl.app O :=
      (P.inl.naturality rleg).symm
    have hi : P.inl.app R ≫ P.ι.app R = W'.obj R ◁ f :=
      NatTrans.congr_app P.inl_ι R
    change P.inl.app R ≫ P.pt.map rleg ≫ cornerTensorReverseBase j f =
      P.inl.app R ≫ P.ι.app R ≫ (pushout.inr (W.map rleg) (j.app R) ▷ B) ≫
        (cornerTensorProduct j f).inr
    rw [← Category.assoc, hn, Category.assoc, cornerTensorReverseBase_inl]
    conv_rhs => rw [← Category.assoc, hi]
    exact cornerTensorProduct_w_inr j f
  · have hn : P.inr.app R ≫ P.pt.map rleg = (W.map rleg ▷ B) ≫ P.inr.app O :=
      (P.inr.naturality rleg).symm
    have hi : P.inr.app R ≫ P.ι.app R = j.app R ▷ B := NatTrans.congr_app P.inr_ι R
    change P.inr.app R ≫ P.pt.map rleg ≫ cornerTensorReverseBase j f =
      P.inr.app R ≫ P.ι.app R ≫ (pushout.inr (W.map rleg) (j.app R) ▷ B) ≫
        (cornerTensorProduct j f).inr
    rw [← Category.assoc, hn, Category.assoc, cornerTensorReverseBase_inr]
    conv_rhs => rw [← Category.assoc, hi]
    rw [← Category.assoc, ← comp_whiskerRight, pushout.condition,
      comp_whiskerRight, Category.assoc]
/-- 概要：pushout-product の相対境界から相対境界の pushout-product への逆向きの射。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
noncomputable def cornerTensorReverse (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    pushout ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) ⟶
      (cornerTensorProduct j f).pt :=
  pushout.desc (cornerTensorReverseBase j f)
    ((pushout.inr (W.map rleg) (j.app R) ▷ B) ≫ (cornerTensorProduct j f).inr)
    (cornerTensorReverse_glue j f)
/-- 概要：交換比較の左成分は中央の pushout の左包含を経由する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorComparison_inl (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (cornerTensorProduct j f).inl ≫ cornerTensorComparison j f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inl.app O ≫ pushout.inl _ _ :=
  (cornerTensorProduct j f).isPushout.inl_desc _ _ _
/-- 概要：交換比較の右成分は直積の貼り合わせの射である。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorComparison_inr (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (cornerTensorProduct j f).inr ≫ cornerTensorComparison j f = cornerTensorMap j f :=
  (cornerTensorProduct j f).isPushout.inr_desc _ _ _
/-- 概要：逆向きの交換比較の左成分は中央の逆射である。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorReverse_inl (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    pushout.inl ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) ≫
      cornerTensorReverse j f = cornerTensorReverseBase j f := pushout.inl_desc _ _ _
/-- 概要：逆向きの交換比較の右成分は延長後の右成分の直積を経由する。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorReverse_inr (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    pushout.inr ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) ≫
      cornerTensorReverse j f =
        (pushout.inr (W.map rleg) (j.app R) ▷ B) ≫ (cornerTensorProduct j f).inr :=
  pushout.inr_desc _ _ _
/-- 概要：交換比較の後で逆向きの比較を合成すると恒等射になる。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorComparison_reverse (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    cornerTensorComparison j f ≫ cornerTensorReverse j f = 𝟙 _ := by
  apply (cornerTensorProduct j f).isPushout.hom_ext
  · rw [← Category.assoc, cornerTensorComparison_inl, Category.assoc,
      cornerTensorReverse_inl, cornerTensorReverseBase_inl, Category.comp_id]
  · rw [← Category.assoc, cornerTensorComparison_inr, Category.comp_id]
    apply (tensorRightCornerPushout j B).hom_ext
    · rw [← Category.assoc, cornerTensorMap_inl, Category.assoc,
        cornerTensorReverse_inl, cornerTensorReverseBase_inr]
    · rw [← Category.assoc, cornerTensorMap_inr, cornerTensorReverse_inr]
/-- 概要：逆向きの比較の後で交換比較を合成すると恒等射になる。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorReverse_comparison (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    cornerTensorReverse j f ≫ cornerTensorComparison j f = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [← Category.assoc, cornerTensorReverse_inl, Category.comp_id]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCornerAt j f O).isPushout.hom_ext
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inl.app O ≫ cornerTensorReverseBase j f ≫
        cornerTensorComparison j f = _
      rw [← Category.assoc, cornerTensorReverseBase_inl, cornerTensorComparison_inl]
      rfl
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).inr.app O ≫ cornerTensorReverseBase j f ≫
        cornerTensorComparison j f = _
      rw [← Category.assoc, cornerTensorReverseBase_inr, Category.assoc,
        cornerTensorComparison_inr, cornerTensorMap_inl]
      rfl
  · rw [← Category.assoc, cornerTensorReverse_inr, Category.assoc,
      cornerTensorComparison_inr, cornerTensorMap_inr, Category.comp_id]
/-- 概要：交換比較は二つの相対境界射を厳密に結ぶ。
方針：pushout の普遍性と直積の自然性を用い、必要な等式は生成成分で確認する。
規約：重み j とパラメーター f に追加の Kan 性や anodyne 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の相対境界と pushout-product の交換同型。 -/
lemma cornerTensorComparison_fac (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    cornerTensorComparison j f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap
        (Functor.whiskerLeft AsSmall.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι) =
      (cornerTensorProduct j f).ι := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f
  let Q := cornerTensorProduct j f
  apply Q.isPushout.hom_ext
  · rw [← Category.assoc, cornerTensorComparison_inl, Category.assoc]
    change P.inl.app O ≫ pushout.inl (P.pt.map rleg) (P.ι.app R) ≫
      pushout.desc (P.ι.app O) ((W' ⊗ (Functor.const _).obj B).map rleg) _ = Q.inl ≫ Q.ι
    rw [pushout.inl_desc, Q.inl_ι]
    exact NatTrans.congr_app P.inl_ι O
  · rw [← Category.assoc, cornerTensorComparison_inr, cornerTensorMap_fac]
    exact Q.inr_ι.symm
/-- 概要：相対境界と pushout-product の二つの順序の間の交換同型。
方針：両方向の貼り合わせの射と、生成成分で確認した逆関係を組み合わせる。
規約：境界射との厳密な可換性は cornerTensorComparison_fac に記録する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の重みの相対境界の移送。 -/
noncomputable def cornerTensorIso (j : W ⟶ W') {A B : SSet.{u}} (f : A ⟶ B) :
    (cornerTensorProduct j f).pt ≅
      pushout ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).pt.map rleg) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι.app R) where
  hom := cornerTensorComparison j f
  inv := cornerTensorReverse j f
  hom_inv_id := cornerTensorComparison_reverse j f
  inv_hom_id := cornerTensorReverse_comparison j f
/-- 概要：中央の相対境界が anodyne なら単射との pushout-product の相対境界も anodyne。
方針：交換同型で相対境界を既存の anodyne な pushout-product へ移す。
規約：パラメーターの射の単射性を明示し、重みの相対境界の anodyne 性を入力にする。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、一脚の fibration 性での重みの制限。 -/
lemma rightCorner_weightedCorner_anodyne (j : W ⟶ W')
    (hj : anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)))
    {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap
      (Functor.whiskerLeft AsSmall.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι)) := by
  let rleg' : Arrow.mk (cornerTensorProduct j f).ι ≅ Arrow.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j f).ι)) :=
    Arrow.isoMk (cornerTensorIso j f) (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact cornerTensorComparison_fac j f)
  exact (anodyneExtensions.arrow_mk_iso_iff rleg').1
    (anodyneExtensions_pushoutObjObjι' (cornerTensorProduct j f) hj)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

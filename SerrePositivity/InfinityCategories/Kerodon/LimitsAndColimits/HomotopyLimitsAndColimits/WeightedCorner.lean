module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：重みの射とパラメーターの境界の相対的な直積を作る。
方針：図式の圏の pushout-product を使い、評価関手で各成分の pushout-product と同定する。
規約：右因子がパラメーター、左因子が重み。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4（Tag 03B5） の重みの制限の全境界の持ち上げ。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：重みの射とパラメーターの射の pushout-product の図式。
方針：図式の圏の直積と pushout を使う。
規約：j : W → W'、f : A → B に対して W'×A と W×B を W×A 上で貼る。
使われ方：Kerodon 7.5.3（Tag 03AP） の端点と重みを同時に固定する延長。 -/
noncomputable def weightedCorner {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    {A B : SSet.{u}} (f : A ⟶ B) :
    (curriedTensor (I ⥤ SSet.{u})).PushoutObjObj j ((Functor.const I).map f) :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- 概要：図式の pushout-product の各成分は単体集合の pushout-product。
方針：評価関手による pushout の保存と直積の成分表示を使う。
規約：既存の pushout の頂点をそのまま使い、別の頂点への同型を選ばない。
使われ方：Kerodon 7.5.3（Tag 03AP） の各段の相対的な anodyne 性。 -/
noncomputable def weightedCornerAt {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    {A B : SSet.{u}} (f : A ⟶ B) (i : I) :
    (curriedTensor SSet.{u}).PushoutObjObj (j.app i) f where
  pt := (weightedCorner j f).pt.obj i
  inl := (weightedCorner j f).inl.app i
  inr := (weightedCorner j f).inr.app i
  isPushout := (weightedCorner j f).isPushout.map ((evaluation I SSet.{u}).obj i)
  ι := (weightedCorner j f).ι.app i
  inl_ι := NatTrans.congr_app (weightedCorner j f).inl_ι i
  inr_ι := NatTrans.congr_app (weightedCorner j f).inr_ι i

/-- 概要：成分ごとに anodyne な重みと単射パラメーターの pushout-product は成分ごとに anodyne。
方針：評価した pushout-product に Mathlib の anodyne と単射の直積の定理を適用する。
規約：重みの図式の間にモデル構造を仮定しない。
使われ方：Kerodon 7.5.3（Tag 03AP）、塔の end の重みの制限の trivial Kan fibration 性。 -/
lemma weightedCorner_obj_anodyne {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i)) {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (i : I) : anodyneExtensions ((weightedCorner j f).ι.app i) :=
  anodyneExtensions_pushoutObjObjι' (weightedCornerAt j f i) (hj i)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

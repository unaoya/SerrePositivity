module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalAnodyneRecognition
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-!
# 元の left cofinal な射の anodyne 反転後の可逆性

概要：Low 命題 3.7 の成分ごとの余終性を元の anodyne 局所化の反転性へ移す。
方針：元の left anodyne・trivial Kan 因子分解と全単射の右類の収縮を使う。
規約：元の射や両対象を置き換えず、単体集合モデルを要求しない。
使われ方：固定右脚の全比較の同じ局所化における反転性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u uH vH

namespace SerrePositivity.EInfinity.FrameHom

open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 概要：元の left anodyne 射は全ホーンに対する anodyne 射（Quillen A）。
方針：全ホーンの右持ち上げ性を左ホーンの生成族へ制限する。
規約：モデル構造や始域の Kan 性は要求しない。
使われ方：元の cofinal 因子分解の左因子の反転。 -/
lemma leftAnodyne_anodyne {A B : SSet.{u}} (i : A ⟶ B) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    SSet.anodyneExtensions i := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro E D p hp
  apply hi p
  intro X Y j hj
  cases hj with
  | intro k _ => exact hp _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ k)

/-- 概要：元の left cofinal な射は任意の anodyne 反転関手で同型（Quillen A）。
方針：元の因子分解の左因子を反転し、右因子には同じ切断と収縮を使う。
規約：射の順方向は元の比較射の像で、モデル構造は入力しない。
使われ方：元の固定右脚の比較の可逆性の判定。 -/
lemma leftCofinal_image_isIso {A B : SSet.{u}} (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f)
    {H : Type uH} [Category.{vH} H] (L : SSet.{u} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map f) := by
  obtain ⟨Z, j, p, _hm, hj, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
  have : IsIso (L.map j) := hL _ (leftAnodyne_anodyne j hj)
  have : IsIso (L.map p) := MonoRightLiftingContraction.image_isIso p hp.mem L hL
  rw [← he, L.map_comp]
  infer_instance

/-- 概要：元の left cofinal な射は同じ anodyne 局所化で可逆（Quillen A）。
方針：元の比較射へ任意の anodyne 反転関手の判定を適用する。
規約：元の射の両端に Kan 性を要求しない。
使われ方：三本矢の全図式の成分ごとの反転性。 -/
lemma leftCofinal_localized_isIso {A B : SSet.{u}} (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) :=
  leftCofinal_image_isIso f hf AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions)

end SerrePositivity.EInfinity.FrameHom

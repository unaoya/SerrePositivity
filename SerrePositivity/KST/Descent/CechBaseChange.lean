module

public import SerrePositivity.KST.Descent.CechPullback
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Čech 底変換の全単体次数の指定比較

## 概要
底変換した射の Čech nerve は、元の Čech nerve を定数図式で底変換したものと同型。

## 方針
恒等射の Čech nerve の増強が実際の同型であることを全次数で証明する。
増強 Čech の Cartesian 正方形をその同型で移す。

## 規約
全ての単体射を保持した図式の同型であり、段ごとの対象同型の存在に弱めない。
前層の値域の Tot やホモトピー引き戻しを構成したとは主張しない。

## 使われ方
論文 補題 3.2 の二重 Čech の幾何と、Fubini・細分のための比較。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- 概要：増強を忘れる関手は幾何的な引き戻しを保つ（論文 補題 3.2）。
方針：Comma の両端の極限から作る極限錐の始域を検査する。
規約：前層の値域のホモトピー極限とは別の通常の関手性。
使われ方：増強 Čech の Cartesian 性を非増強図式へ移す。 -/
noncomputable instance augmentedDrop_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (SimplicialObject.Augmented.drop (C := C)) where
  preservesLimit {K} :=
    preservesLimit_of_preserves_limit_cone
      (Comma.coneOfPreservesIsLimit K (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

/-- 概要：恒等射の Čech 各段の増強は同型（論文 補題 3.2）。
方針：恒等射の族の wide pullback の普遍性で逆射を構成する。
規約：全ての非増強単体次数で検査する。
使われ方：恒等射の Čech nerve と定数図式の自然同型。 -/
noncomputable instance identityCech_augmentation_app_isIso (X : C) (n : SimplexCategoryᵒᵖ) :
    IsIso ((Arrow.mk (𝟙 X)).augmentedCechNerve.hom.app n) := by
  let l : X ⟶ (Arrow.mk (𝟙 X)).cechNerve.obj n :=
    WidePullback.lift (𝟙 X) (fun _ ↦ 𝟙 X) (fun _ ↦ by simp)
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply WidePullback.hom_ext
    · intro j
      have hp : WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ 𝟙 X) j =
          WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ 𝟙 X) :=
        (Category.comp_id _).symm.trans (WidePullback.π_arrow _ j)
      exact (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (WidePullback.lift_π _ _ _ _ j)).trans
          ((Category.comp_id _).trans ((Category.id_comp _).trans hp).symm))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (WidePullback.lift_base _ _ _ _)).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm))
  · exact WidePullback.lift_base _ _ _ _

/-- 概要：恒等射の Čech nerve は定数図式と自然同型（論文 補題 3.2）。
方針：全ての増強成分の同型性から、増強そのものを自然同型にする。
規約：同型の hom は指定された増強写像。
使われ方：底変換比較の両基底を定数図式へ移す。 -/
noncomputable def identityCechIso (X : C) :
    (Arrow.mk (𝟙 X)).cechNerve ≅ (SimplicialObject.const C).obj X := by
  letI (n : SimplexCategoryᵒᵖ) : IsIso ((Arrow.mk (𝟙 X)).augmentedCechNerve.hom.app n) :=
    identityCech_augmentation_app_isIso X n
  have h : IsIso (Arrow.mk (𝟙 X)).augmentedCechNerve.hom :=
    NatIso.isIso_of_isIso_app _
  exact @asIso _ _ _ _ (Arrow.mk (𝟙 X)).augmentedCechNerve.hom h

/-- 概要：Arrow の射からの Čech 比較は増強と可換（論文 補題 3.2）。
方針：実際の増強 Čech の射の可換性をそのまま使う。
規約：指定射の全ての単体次数と自然性を保持する。
使われ方：底変換正方形の四辺の増強との比較。 -/
theorem mapCechNerve_augmentation {f g : Arrow C} (a : f ⟶ g) :
    Arrow.mapCechNerve a ≫ g.augmentedCechNerve.hom =
      f.augmentedCechNerve.hom ≫ (SimplicialObject.const C).map a.right :=
  (Arrow.mapAugmentedCechNerve a).w

variable {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)

/-- 概要：Čech nerve の底変換は定数図式での実際の引き戻し（論文 補題 3.2）。
方針：増強 Čech の引き戻しを忘却し、恒等射の Čech の自然同型で移す。
規約：幾何的な図式の Cartesian 性であり、前層の実降下は別条件。
使われ方：二重 Čech と段ごとの切断つき降下の比較。 -/
theorem baseChangeCech_isPullback :
    IsPullback (Arrow.mapCechNerve (baseChangeArrowToOriginal f g))
      (Arrow.mk (pullback.snd f g)).augmentedCechNerve.hom
      (Arrow.mk f).augmentedCechNerve.hom ((SimplicialObject.const C).map g) := by
  let F := SimplicialObject.Augmented.drop (C := C)
  have h := (baseChangeAugmentedCech_isPullback f g).map F
  apply h.of_iso (Iso.refl _) (Iso.refl _) (identityCechIso Z) (identityCechIso Y)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (mapCechNerve_augmentation (baseChangeArrowToIdentity f g)).trans
      ((congrArg (_ ≫ ·) ((SimplicialObject.const C).map_id Z)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  · exact (mapCechNerve_augmentation
      (Arrow.homMk f (𝟙 Y) : Arrow.mk f ⟶ Arrow.mk (𝟙 Y))).trans
      ((congrArg (_ ≫ ·) ((SimplicialObject.const C).map_id Y)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  · exact mapCechNerve_augmentation
      (Arrow.homMk g g : Arrow.mk (𝟙 Z) ⟶ Arrow.mk (𝟙 Y))

/-- 概要：底変換した Čech nerve の全単体次数の標準同型（論文 補題 3.2）。
方針：指定四辺の Cartesian 性から、指定引き戻しとの標準同型を取る。
規約：同型は元の Čech への射と増強の二射影を保つ。
使われ方：Fubini・細分の際に用いる幾何的な図式の比較。 -/
noncomputable def baseChangeCechIso :
    (Arrow.mk (pullback.snd f g)).cechNerve ≅
      pullback (Arrow.mk f).augmentedCechNerve.hom ((SimplicialObject.const C).map g) :=
  (baseChangeCech_isPullback f g).isoPullback

end SerrePositivity.KST.Descent

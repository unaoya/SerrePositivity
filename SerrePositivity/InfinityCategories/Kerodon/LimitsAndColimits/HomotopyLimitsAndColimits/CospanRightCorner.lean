module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanDiagramExtension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：右脚の fibration 性を使わずに cospan への自然変換を延長する相対的な条件。
方針：右成分を先に延長し、その値を中央成分の pushout の境界に組み込む。
規約：中央の相対境界の持ち上げ性は明示し、成分ごとの anodyne 性だけで代用しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、一脚だけが fibration の引き戻しの重みの比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：右成分を延長した後で中央成分を延長するための相対的な境界射。
方針：A(one) と B(right) を A(right) 上で貼り、自然性から B(one) へ写す。
規約：図式の射 j : A → B の右脚の可換四角形を使う。
使われ方：Kerodon 7.5.3（Tag 03AP） の一脚の fibration 性での相対的な延長。 -/
noncomputable def cospanRightCornerMap {A B : WalkingCospan ⥤ SSet.{u}} (j : A ⟶ B) :
    pushout (A.map WalkingCospan.Hom.inr) (j.app .right) ⟶ B.obj .one :=
  pushout.desc (j.app .one) (B.map WalkingCospan.Hom.inr)
    (j.naturality WalkingCospan.Hom.inr)

/-- 概要：右成分と中央の相対境界の持ち上げから、左脚だけを使って cospan を延長できる。
方針：右成分を延長し、中央の二つの固定値を pushout 上で貼り、最後に左脚を相対充填する。
規約：右脚 H(right) → H(one) に fibration 性や持ち上げ性を要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の一脚だけが fibration の引き戻しの準備。 -/
lemma exists_cospan_extension_of_rightCorner {A B H : WalkingCospan ⥤ SSet.{u}}
    (j : A ⟶ B)
    [HasLiftingProperty (j.app .right) (terminal.from (H.obj .right))]
    [HasLiftingProperty (cospanRightCornerMap j) (terminal.from (H.obj .one))]
    [HasLiftingProperty (j.app .left) (H.map WalkingCospan.Hom.inl)]
    (a : A ⟶ H) : ∃ b : B ⟶ H, j ≫ b = a := by
  let sr : CommSq (a.app .right) (j.app .right) (terminal.from (H.obj .right))
      (terminal.from (B.obj .right)) := ⟨terminal.hom_ext _ _⟩
  have hw : A.map WalkingCospan.Hom.inr ≫ a.app .one =
      j.app .right ≫ (sr.lift ≫ H.map WalkingCospan.Hom.inr) := by
    rw [← Category.assoc, sr.fac_left]
    exact a.naturality _
  let z := pushout.desc (a.app .one) (sr.lift ≫ H.map WalkingCospan.Hom.inr) hw
  let sz : CommSq z (cospanRightCornerMap j) (terminal.from (H.obj .one))
      (terminal.from (B.obj .one)) := ⟨terminal.hom_ext _ _⟩
  have h₀ : j.app .one ≫ sz.lift = a.app .one := by
    calc
      _ = (pushout.inl (A.map WalkingCospan.Hom.inr) (j.app .right) ≫
          cospanRightCornerMap j) ≫ sz.lift := by
        simp only [cospanRightCornerMap, pushout.inl_desc]
      _ = _ := by rw [Category.assoc, sz.fac_left, pushout.inl_desc]
  have hr : B.map WalkingCospan.Hom.inr ≫ sz.lift =
      sr.lift ≫ H.map WalkingCospan.Hom.inr := by
    calc
      _ = (pushout.inr (A.map WalkingCospan.Hom.inr) (j.app .right) ≫
          cospanRightCornerMap j) ≫ sz.lift := by
        simp only [cospanRightCornerMap, pushout.inr_desc]
      _ = _ := by rw [Category.assoc, sz.fac_left, pushout.inr_desc]
  have hl : a.app .left ≫ H.map WalkingCospan.Hom.inl =
      j.app .left ≫ (B.map WalkingCospan.Hom.inl ≫ sz.lift) := by
    rw [← a.naturality WalkingCospan.Hom.inl, ← h₀, ← Category.assoc,
      j.naturality WalkingCospan.Hom.inl, Category.assoc]
  let sl : CommSq (a.app .left) (j.app .left) (H.map WalkingCospan.Hom.inl)
      (B.map WalkingCospan.Hom.inl ≫ sz.lift) := ⟨hl⟩
  refine ⟨cospanHomMk sz.lift sl.lift sr.lift sl.fac_right.symm hr, ?_⟩
  apply NatTrans.ext
  funext i
  rcases i with (_ | _ | _)
  · exact h₀
  · exact sl.fac_left
  · exact sr.fac_left

/-- 概要：中央と右端が Kan で左脚が fibration なら、相対境界が anodyne な射に沿って延長できる。
方針：必要な三つの持ち上げ性を二つの Kan 性と左脚の Fibration 性から得る。
規約：係数の宇宙へ持ち上げた cospan を使い、中央の相対境界の anodyne 性を明示する。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、一脚の fibration 性での重みの比較の入力。 -/
lemma exists_resized_cospan_extension_of_rightCorner
    {A B H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : A ⟶ B)
    (hl : anodyneExtensions (j.app (AsSmall.up.obj .left)))
    (hr : anodyneExtensions (j.app (AsSmall.up.obj .right)))
    (h₀ : anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)))
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    (a : A ⟶ H) : ∃ b : B ⟶ H, j ≫ b = a := by
  have : Fibration ((AsSmall.up ⋙ H).map WalkingCospan.Hom.inl) :=
    inferInstanceAs (Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl)))
  have : KanComplex ((AsSmall.up ⋙ H).obj .one) :=
    inferInstanceAs (KanComplex (H.obj (AsSmall.up.obj .one)))
  have : KanComplex ((AsSmall.up ⋙ H).obj .right) :=
    inferInstanceAs (KanComplex (H.obj (AsSmall.up.obj .right)))
  have : HasLiftingProperty ((Functor.whiskerLeft AsSmall.up j).app .left)
      ((AsSmall.up ⋙ H).map WalkingCospan.Hom.inl) :=
    hl _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  have : HasLiftingProperty ((Functor.whiskerLeft AsSmall.up j).app .right)
      (terminal.from ((AsSmall.up ⋙ H).obj .right)) :=
    hr _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  have : HasLiftingProperty (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j))
      (terminal.from ((AsSmall.up ⋙ H).obj .one)) :=
    h₀ _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  obtain ⟨b, hb⟩ := exists_cospan_extension_of_rightCorner
    (Functor.whiskerLeft AsSmall.up j) (Functor.whiskerLeft AsSmall.up a)
  let b' : B ⟶ H :=
    { app := fun i => b.app (AsSmall.down.obj i)
      naturality := fun _ _ f => b.naturality (AsSmall.down.map f) }
  refine ⟨b', ?_⟩
  apply NatTrans.ext
  funext i
  exact congrArg (fun η => η.app (AsSmall.down.obj i)) hb

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

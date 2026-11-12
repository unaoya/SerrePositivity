module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.WeightedTowerKan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：cospan の中央成分を固定した自然変換の相対的延長。
方針：左右の持ち上げ問題を独立に解き、二つの三角形から自然変換を作る。
規約：中央成分と既存の部分図式での値を厳密に保つ。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、引き戻しの重み付き end の持ち上げ。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：cospan の両脚に対する持ち上げ性から中央成分を保って自然変換を延長できる。
方針：左右の成分で可換四角形を作り、その持ち上げを cospanHomMk で束ねる。
規約：Kan 性や fibration 性は仮定せず、必要な二つの持ち上げ性を明示する。
使われ方：Kerodon 7.5.3（Tag 03AP） の有限の相対的な図式の延長。 -/
lemma exists_cospan_diagram_extension {A B H : WalkingCospan ⥤ SSet.{u}}
    (j : A ⟶ B)
    [HasLiftingProperty (j.app .left) (H.map WalkingCospan.Hom.inl)]
    [HasLiftingProperty (j.app .right) (H.map WalkingCospan.Hom.inr)]
    (a : A ⟶ H) (f₀ : B.obj .one ⟶ H.obj .one)
    (h₀ : j.app .one ≫ f₀ = a.app .one) :
    ∃ b : B ⟶ H, j ≫ b = a ∧ b.app .one = f₀ := by
  have hw {i : WalkingCospan} (t : i ⟶ .one) :
      a.app i ≫ H.map t = j.app i ≫ (B.map t ≫ f₀) := by
    rw [← a.naturality t, ← h₀, ← Category.assoc, j.naturality t, Category.assoc]
  let sl : CommSq (a.app .left) (j.app .left) (H.map WalkingCospan.Hom.inl)
      (B.map WalkingCospan.Hom.inl ≫ f₀) := ⟨hw _⟩
  let sr : CommSq (a.app .right) (j.app .right) (H.map WalkingCospan.Hom.inr)
      (B.map WalkingCospan.Hom.inr ≫ f₀) := ⟨hw _⟩
  let b := cospanHomMk f₀ sl.lift sr.lift sl.fac_right.symm sr.fac_right.symm
  refine ⟨b, ?_, rfl⟩
  apply NatTrans.ext
  funext i
  rcases i with (_ | _ | _)
  · exact h₀
  · exact sl.fac_left
  · exact sr.fac_left

/-- 概要：係数の宇宙へ持ち上げた cospan でも中央成分を保って自然変換を延長できる。
方針：AsSmall.up で通常の cospan に制限してから、対象と射の down で戻す。
規約：重み付き end と同じ宇宙の AsSmall.{u} WalkingCospan を使う。
使われ方：Kerodon 7.5.3（Tag 03AP）、任意の宇宙の単体集合の cospan。 -/
lemma exists_resized_cospan_diagram_extension
    {A B H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : A ⟶ B)
    [HasLiftingProperty (j.app (AsSmall.up.obj .left))
      (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    [HasLiftingProperty (j.app (AsSmall.up.obj .right))
      (H.map (AsSmall.up.map WalkingCospan.Hom.inr))]
    (a : A ⟶ H) (f₀ : B.obj (AsSmall.up.obj .one) ⟶ H.obj (AsSmall.up.obj .one))
    (h₀ : j.app (AsSmall.up.obj .one) ≫ f₀ = a.app (AsSmall.up.obj .one)) :
    ∃ b : B ⟶ H, j ≫ b = a ∧ b.app (AsSmall.up.obj .one) = f₀ := by
  have : HasLiftingProperty ((Functor.whiskerLeft AsSmall.up j).app .left)
      ((AsSmall.up ⋙ H).map WalkingCospan.Hom.inl) :=
    inferInstanceAs (HasLiftingProperty (j.app (AsSmall.up.obj .left))
      (H.map (AsSmall.up.map WalkingCospan.Hom.inl)))
  have : HasLiftingProperty ((Functor.whiskerLeft AsSmall.up j).app .right)
      ((AsSmall.up ⋙ H).map WalkingCospan.Hom.inr) :=
    inferInstanceAs (HasLiftingProperty (j.app (AsSmall.up.obj .right))
      (H.map (AsSmall.up.map WalkingCospan.Hom.inr)))
  obtain ⟨b, hb, hb₀⟩ := exists_cospan_diagram_extension
    (Functor.whiskerLeft AsSmall.up j) (Functor.whiskerLeft AsSmall.up a) f₀ h₀
  let b' : B ⟶ H :=
    { app := fun i => b.app (AsSmall.down.obj i)
      naturality := fun _ _ f => b.naturality (AsSmall.down.map f) }
  refine ⟨b', ?_, hb₀⟩
  apply NatTrans.ext
  funext i
  exact congrArg (fun η => η.app (AsSmall.down.obj i)) hb

/-- 概要：中央が Kan、両脚が fibration の cospan に対して成分ごとの anodyne な延長が可能。
方針：中央成分を Kan 性で延長し、左右の fibration の持ち上げで自然性を保つ。
規約：この定理は両脚の Fibration 性を要求する。
使われ方：Kerodon 7.5.3（Tag 03AP） の isofibrant な cospan の重みの比較。 -/
lemma exists_resized_cospan_extension_of_anodyne
    {A B H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : A ⟶ B)
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inr))]
    (a : A ⟶ H) : ∃ b : B ⟶ H, j ≫ b = a := by
  have : HasLiftingProperty (j.app (AsSmall.up.obj .left))
      (H.map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
    hj _ _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  have : HasLiftingProperty (j.app (AsSmall.up.obj .right))
      (H.map (AsSmall.up.map WalkingCospan.Hom.inr)) :=
    hj _ _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  have : HasLiftingProperty (j.app (AsSmall.up.obj .one))
      (terminal.from (H.obj (AsSmall.up.obj .one))) :=
    hj _ _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  let sq : CommSq (a.app (AsSmall.up.obj .one)) (j.app (AsSmall.up.obj .one))
      (terminal.from (H.obj (AsSmall.up.obj .one)))
      (terminal.from (B.obj (AsSmall.up.obj .one))) := ⟨terminal.hom_ext _ _⟩
  obtain ⟨b, hb, _⟩ := exists_resized_cospan_diagram_extension j a sq.lift sq.fac_left
  exact ⟨b, hb⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

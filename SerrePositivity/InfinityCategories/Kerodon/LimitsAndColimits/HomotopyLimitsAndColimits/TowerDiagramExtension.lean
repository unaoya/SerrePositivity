module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.TowerExtension
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：逆向きの可算塔に対する、始域の図式も変化する相対的な延長。
方針：各段の持ち上げを前段の射と下の図式の遷移の合成の上で選ぶ。
規約：添字の持ち上げも扱い、自然性を前提にした独立な段ごとの選択では代用しない。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4（Tag 03B5） の塔の重み付き切断空間の Kan 性。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：変化する始域の図式の射に沿って、零段の延長から塔の自然変換を延長する。
方針：自然性から各段の持ち上げ問題を作り、帰納的に選んだ射を自然変換にまとめる。
規約：必要なのは各後続段の射と標的の遷移の間の持ち上げ性。
使われ方：Kerodon 7.5.3（Tag 03AP）、重み付き切断のホーンと境界の相対充填。 -/
lemma exists_tower_diagram_extension {A B H : ℕᵒᵖ ⥤ SSet.{u}} (j : A ⟶ B)
    [∀ n : ℕ, HasLiftingProperty (j.app (Opposite.op (n + 1)))
      (H.map (homOfLE (Nat.le_succ n)).op)]
    (a : A ⟶ H) (f₀ : B.obj (Opposite.op 0) ⟶ H.obj (Opposite.op 0))
    (h₀ : j.app (Opposite.op 0) ≫ f₀ = a.app (Opposite.op 0)) :
    ∃ b : B ⟶ H, j ≫ b = a ∧ b.app (Opposite.op 0) = f₀ := by
  classical
  let Fill (n : ℕ) := {f : B.obj (Opposite.op n) ⟶ H.obj (Opposite.op n) //
    j.app (Opposite.op n) ≫ f = a.app (Opposite.op n)}
  have step (n : ℕ) (f : Fill n) : ∃ g : Fill (n + 1),
      g.val ≫ H.map (homOfLE (Nat.le_succ n)).op =
        B.map (homOfLE (Nat.le_succ n)).op ≫ f.val := by
    let t := (homOfLE (Nat.le_succ n)).op
    have hw : a.app (Opposite.op (n + 1)) ≫ H.map t =
        j.app (Opposite.op (n + 1)) ≫ (B.map t ≫ f.val) := by
      calc
        _ = A.map t ≫ a.app (Opposite.op n) := (a.naturality t).symm
        _ = A.map t ≫ (j.app (Opposite.op n) ≫ f.val) :=
          congrArg (fun g ↦ A.map t ≫ g) f.property.symm
        _ = _ := by rw [← Category.assoc, j.naturality t, Category.assoc]
    let sq : CommSq (a.app (Opposite.op (n + 1))) (j.app (Opposite.op (n + 1)))
        (H.map t) (B.map t ≫ f.val) := ⟨hw⟩
    exact ⟨⟨sq.lift, sq.fac_left⟩, sq.fac_right⟩
  choose next hnext using step
  let f : ∀ n, Fill n := Nat.rec ⟨f₀, h₀⟩ next
  have hf (n : ℕ) : (f (n + 1)).val ≫ H.map (homOfLE (Nat.le_succ n)).op =
      B.map (homOfLE (Nat.le_succ n)).op ≫ (f n).val := hnext n (f n)
  let b : B ⟶ H := NatTrans.ofOpSequence (fun n ↦ (f n).val) (fun n ↦ (hf n).symm)
  refine ⟨b, ?_, rfl⟩
  apply NatTrans.ext
  funext n
  exact (f n.unop).property

/-- 概要：添字を持ち上げた塔でも、成分ごとの持ち上げ性から自然変換を延長できる。
方針：AsSmall.up で通常の可算塔へ戻し、得た自然変換を対象と射の down で戻す。
規約：係数の宇宙 u に合わせた小圏 AsSmall.{u} ℕᵒᵖ を使う。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の SSet.{u} の重み付き end への適用。 -/
lemma exists_resized_tower_diagram_extension
    {A B H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : A ⟶ B)
    [∀ n : ℕ, HasLiftingProperty (j.app (AsSmall.up.obj (Opposite.op (n + 1))))
      (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]
    (a : A ⟶ H)
    (f₀ : B.obj (AsSmall.up.obj (Opposite.op 0)) ⟶ H.obj (AsSmall.up.obj (Opposite.op 0)))
    (h₀ : j.app (AsSmall.up.obj (Opposite.op 0)) ≫ f₀ = a.app (AsSmall.up.obj (Opposite.op 0))) :
    ∃ b : B ⟶ H, j ≫ b = a ∧ b.app (AsSmall.up.obj (Opposite.op 0)) = f₀ := by
  have (n : ℕ) : HasLiftingProperty
      ((Functor.whiskerLeft AsSmall.up j).app (Opposite.op (n + 1)))
      ((AsSmall.up ⋙ H).map (homOfLE (Nat.le_succ n)).op) :=
    inferInstanceAs (HasLiftingProperty (j.app (AsSmall.up.obj (Opposite.op (n + 1))))
      (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)))
  obtain ⟨b, hb, hb₀⟩ := exists_tower_diagram_extension
    (Functor.whiskerLeft AsSmall.up j) (Functor.whiskerLeft AsSmall.up a) f₀ h₀
  let b' : B ⟶ H :=
    { app := fun n ↦ b.app (AsSmall.down.obj n)
      naturality := fun n m f ↦ b.naturality (AsSmall.down.map f) }
  refine ⟨b', ?_, hb₀⟩
  apply NatTrans.ext
  funext n
  exact congrArg (fun η ↦ η.app (AsSmall.down.obj n)) hb

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

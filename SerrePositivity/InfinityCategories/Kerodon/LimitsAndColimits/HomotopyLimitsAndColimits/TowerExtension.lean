module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.Presheaf

/-!
概要：逆向きの可算塔への射の整合的な延長。
方針：零段の延長を固定し、各遷移の持ち上げ性で次の段を帰納的に選ぶ。
規約：各段で独立に延長を選ばず、全ての遷移と整合する自然変換を構成する。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4（Tag 03B5） の fibration の塔の strict 極限の充填。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：塔の各遷移が j の持ち上げ性を持てば、零段の延長を全段へ整合的に延長できる。
方針：既知の段を下辺とする持ち上げ問題を解き、NatTrans.ofOpSequence で自然性を得る。
規約：任意の射 j を扱い、モノ射やモデル構造は前提にしない。
使われ方：Kerodon 7.5.3（Tag 03AP）、fibration の塔の極限の Kan 性。 -/
lemma exists_tower_extension (H : ℕᵒᵖ ⥤ SSet.{u}) {A B : SSet.{u}} (j : A ⟶ B)
    [∀ n : ℕ, HasLiftingProperty j (H.map (homOfLE (Nat.le_succ n)).op)]
    (a : (Functor.const ℕᵒᵖ).obj A ⟶ H) (f₀ : B ⟶ H.obj (Opposite.op 0))
    (h₀ : j ≫ f₀ = a.app (Opposite.op 0)) :
    ∃ b : (Functor.const ℕᵒᵖ).obj B ⟶ H,
      (Functor.const ℕᵒᵖ).map j ≫ b = a ∧ b.app (Opposite.op 0) = f₀ := by
  classical
  let Fill (n : ℕ) := {f : B ⟶ H.obj (Opposite.op n) // j ≫ f = a.app (Opposite.op n)}
  have step (n : ℕ) (f : Fill n) :
      ∃ g : Fill (n + 1), g.val ≫ H.map (homOfLE (Nat.le_succ n)).op = f.val := by
    have h : a.app (Opposite.op (n + 1)) ≫ H.map (homOfLE (Nat.le_succ n)).op =
        a.app (Opposite.op n) := by
      simpa using (a.naturality (homOfLE (Nat.le_succ n)).op).symm
    let sq : CommSq (a.app (Opposite.op (n + 1))) j
        (H.map (homOfLE (Nat.le_succ n)).op) f.val := ⟨h.trans f.property.symm⟩
    exact ⟨⟨sq.lift, sq.fac_left⟩, sq.fac_right⟩
  choose next hnext using step
  let f : ∀ n, Fill n := Nat.rec ⟨f₀, h₀⟩ next
  have hf (n : ℕ) :
      (f (n + 1)).val ≫ H.map (homOfLE (Nat.le_succ n)).op = (f n).val :=
    hnext n (f n)
  let b : (Functor.const ℕᵒᵖ).obj B ⟶ H :=
    NatTrans.ofOpSequence (fun n ↦ (f n).val) (fun n ↦ by simpa using (hf n).symm)
  refine ⟨b, ?_, rfl⟩
  apply NatTrans.ext
  funext n
  exact (f n.unop).property

/-- 概要：全ての遷移が j の持ち上げ性を持つ塔の極限の零段への射影も持ち上げ性を持つ。
方針：下辺で与えられた零段の延長から整合的な全段の延長を作り、極限へ持ち上げる。
規約：零段の対象の fibrancy や j の単射性は不要。
使われ方：Kerodon 7.5.3（Tag 03AP）、fibration の塔と相対的な極限の計算。 -/
lemma hasLiftingProperty_towerLimitπ_zero (H : ℕᵒᵖ ⥤ SSet.{u}) {A B : SSet.{u}}
    (j : A ⟶ B)
    [∀ n : ℕ, HasLiftingProperty j (H.map (homOfLE (Nat.le_succ n)).op)] :
    HasLiftingProperty j (limit.π H (Opposite.op 0)) where
  sq_hasLift {a b} sq := by
    let a' : (Functor.const ℕᵒᵖ).obj A ⟶ H :=
      (Functor.const ℕᵒᵖ).map a ≫ (limit.cone H).π
    obtain ⟨c, hc, hc₀⟩ := exists_tower_extension H j a' b sq.w.symm
    refine CommSq.HasLift.mk' { l := limit.lift H ⟨B, c⟩, fac_left := ?_, fac_right := ?_ }
    · apply limit.hom_ext
      intro n
      rw [Category.assoc, limit.lift_π]
      exact congrArg (fun η ↦ η.app n) hc
    · rw [limit.lift_π]
      exact hc₀

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

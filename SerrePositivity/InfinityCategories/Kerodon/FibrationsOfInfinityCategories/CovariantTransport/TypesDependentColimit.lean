module

public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
概要：型の余極限上の依存する値の貼り合わせ。
方針：依存和を値域とする通常の cocone を貼り、第一成分が恒等射であることを使う。
規約：これは通常の型の余極限の補題であり、∞ 余極限の主張ではない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の各次数での pullback と余極限の交換。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：余極限の各項の上の互換な依存値は余極限上へ貼れる。
方針：依存和への cocone を通常の余極限から降ろし、射影との可換性で値を移送する。
規約：互換性は各値の HEq で述べ、底の等式は cocone の自然性が与える。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、固定した底への pullback の余極限保存。 -/
lemma types_exists_dependentDesc {J : Type v} [Category.{w} J] {D : J ⥤ Type u}
    (c : Cocone D) (hc : IsColimit c) (P : c.pt → Type u)
    (a : ∀ j (x : D.obj j), P (c.ι.app j x))
    (ha : ∀ {j k} (f : j ⟶ k) (x : D.obj j), HEq (a k (D.map f x)) (a j x)) :
    ∃ b : ∀ z, P z, ∀ j (x : D.obj j), b (c.ι.app j x) = a j x := by
  let s : Cocone D :=
    { pt := Σ z, P z
      ι :=
        { app j := ↾fun x ↦ ⟨c.ι.app j x, a j x⟩
          naturality j k f := by
            apply ConcreteCategory.hom_ext
            intro x
            apply Sigma.ext
            · exact ConcreteCategory.congr_hom (c.w f) x
            · exact ha f x } }
  let d := hc.desc s
  have hd : d ≫ (↾Sigma.fst : s.pt ⟶ c.pt) = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc, hc.fac]
    rfl
  have hd₀ (z : c.pt) : (d z).1 = z := by
    simpa using ConcreteCategory.congr_hom (C := Type u) hd z
  let b (z : c.pt) : P z := hd₀ z ▸ (d z).2
  refine ⟨b, ?_⟩
  intro j x
  have h : d (c.ι.app j x) = ⟨c.ι.app j x, a j x⟩ :=
    ConcreteCategory.congr_hom (hc.fac s j) x
  dsimp only [b]
  have hsnd : HEq (d (c.ι.app j x)).2 (a j x) := (Sigma.mk.inj h).2
  exact eq_of_heq ((eqRec_heq (hd₀ (c.ι.app j x)) (d (c.ι.app j x)).2).trans hsnd)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

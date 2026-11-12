module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.TypesDependentColimit
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Data.Subtype

/-!
概要：型の余極限の cocone を pullback した cocone の余極限性。
方針：各 fiber 上の写像を依存する値の貼り合わせで降ろし、射の一意性を共同全射性で示す。
規約：図式の形や遷移射の単射性に制限を課さない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の次数ごとの余極限保存。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：余極限の cocone の各脚を pullback した cocone は余極限。
方針：任意の cocone の値を fiber 上の関数として貼り、pullback の一意性で計算則を確認する。
規約：底の型と各型は宇宙 u、添字の宇宙は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、単体集合の相対 join のセルと骨格への拡張。 -/
noncomputable def types_isColimit_of_pullback {J : Type v} [Category.{w} J]
    {D E : J ⥤ Type u} (c : Cocone D) (hc : IsColimit c) (d : Cocone E)
    (α : E ⟶ D) (f : d.pt ⟶ c.pt)
    (hp : ∀ j, IsPullback (d.ι.app j) (α.app j) f (c.ι.app j)) : IsColimit d := by
  classical
  let l (j : J) (x : D.obj j) (y : {y : d.pt // f y = c.ι.app j x}) : E.obj j :=
    (Types.exists_of_isPullback (hp j) y.val x y.property).choose
  have hl₁ (j : J) (x : D.obj j) (y : {y : d.pt // f y = c.ι.app j x}) :
      d.ι.app j (l j x y) = y.val :=
    (Types.exists_of_isPullback (hp j) y.val x y.property).choose_spec.1
  have hl₂ (j : J) (x : D.obj j) (y : {y : d.pt // f y = c.ι.app j x}) :
      α.app j (l j x y) = x :=
    (Types.exists_of_isPullback (hp j) y.val x y.property).choose_spec.2
  have hsurj (y : d.pt) : ∃ (j : J) (x : E.obj j), d.ι.app j x = y := by
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective D hc (f y)
    exact ⟨j, l j x ⟨y, hx.symm⟩, hl₁ j x ⟨y, hx.symm⟩⟩
  have hex (s : Cocone E) : ∃ m : d.pt ⟶ s.pt, ∀ j, d.ι.app j ≫ m = s.ι.app j := by
    let P (z : c.pt) := {y : d.pt // f y = z} → s.pt
    let a (j : J) (x : D.obj j) : P (c.ι.app j x) := fun y ↦ s.ι.app j (l j x y)
    have ha {j k : J} (q : j ⟶ k) (x : D.obj j) : HEq (a k (D.map q x)) (a j x) := by
      have hcx : (c.ι.app k (D.map q x) : c.pt) = c.ι.app j x := by
        change (D.map q ≫ c.ι.app k) x = c.ι.app j x
        exact ConcreteCategory.congr_hom (c.w q) x
      apply Function.hfunext
      · exact congrArg (fun z ↦ {y : d.pt // f y = z}) hcx
      · intro y y' hy
        have hyv : y.val = y'.val := (Subtype.heq_iff_coe_eq (fun z ↦ by
          rw [hcx])).mp hy
        have he : E.map q (l j x y') = l k (D.map q x) y := by
          apply Types.ext_of_isPullback (hp k)
          · have hn := ConcreteCategory.congr_hom (d.w q) (l j x y')
            change d.ι.app k (E.map q (l j x y')) = d.ι.app j (l j x y') at hn
            exact hn.trans ((hl₁ j x y').trans (hyv.symm.trans (hl₁ k (D.map q x) y).symm))
          · have hn := ConcreteCategory.congr_hom (α.naturality q) (l j x y')
            change α.app k (E.map q (l j x y')) = D.map q (α.app j (l j x y')) at hn
            exact hn.trans (congrArg (fun z ↦ D.map q z) (hl₂ j x y')) |>.trans
              (hl₂ k (D.map q x) y).symm
        apply heq_of_eq
        change s.ι.app k (l k (D.map q x) y) = s.ι.app j (l j x y')
        rw [← he]
        exact ConcreteCategory.congr_hom (s.w q) (l j x y')
    obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.types_exists_dependentDesc c hc P a ha
    have hb' (z : c.pt) (y : d.pt) (hy : f y = z) :
        b (f y) ⟨y, rfl⟩ = b z ⟨y, hy⟩ := by
      subst z
      rfl
    refine ⟨↾fun y ↦ b (f y) ⟨y, rfl⟩, ?_⟩
    intro j
    apply ConcreteCategory.hom_ext
    intro x
    have hw := ConcreteCategory.congr_hom (hp j).w x
    change f (d.ι.app j x) = c.ι.app j (α.app j x) at hw
    change b (f (d.ι.app j x)) ⟨d.ι.app j x, rfl⟩ = s.ι.app j x
    rw [hb' _ _ hw, hb]
    change s.ι.app j (l j (α.app j x) ⟨d.ι.app j x, hw⟩) = s.ι.app j x
    congr 1
    apply Types.ext_of_isPullback (hp j)
    · exact hl₁ _ _ _
    · exact hl₂ _ _ _
  exact
    { desc := fun s ↦ (hex s).choose
      fac := fun s j ↦ (hex s).choose_spec j
      uniq := by
        intro s m hm
        apply ConcreteCategory.hom_ext
        intro y
        obtain ⟨j, x, rfl⟩ := hsurj y
        exact (ConcreteCategory.congr_hom (hm j) x).trans
          (ConcreteCategory.congr_hom ((hex s).choose_spec j) x).symm }

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

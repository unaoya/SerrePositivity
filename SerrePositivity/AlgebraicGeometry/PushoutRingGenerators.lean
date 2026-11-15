module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
概要：可換環の pushout の生成元と、底変換による生成元の像を比較する。
方針：二つの像を含む部分環への普遍射を作り、その包含との合成を恒等射と比較する。
規約：生成元は部分環の closure で表し、環の構造射を変えない。
使われ方：Stacks 07RH の有限生成元を底変換の各段へ供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u v

/-- 可換環の pushout は二つの構造射の像で生成される。 -/
theorem closure_range_union_eq_top_of_isPushout
    {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (h : IsPushout f g i j) :
    Subring.closure (Set.range i ∪ Set.range j) = ⊤ := by
  let K := Subring.closure (Set.range i ∪ Set.range j)
  let l : B ⟶ CommRingCat.of K := CommRingCat.ofHom
    (i.hom.codRestrict K (fun x ↦ Subring.subset_closure (.inl ⟨x, rfl⟩)))
  let r : C ⟶ CommRingCat.of K := CommRingCat.ofHom
    (j.hom.codRestrict K (fun x ↦ Subring.subset_closure (.inr ⟨x, rfl⟩)))
  have w : f ≫ l = g ≫ r := by
    ext x
    exact congrArg (fun z : A ⟶ P ↦ z x) h.w
  let d := h.desc l r w
  have hd : d ≫ CommRingCat.ofHom K.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc]
      rfl
    · rw [← Category.assoc, h.inr_desc]
      rfl
  apply top_unique
  intro x _
  have hx := congrArg (fun z : P ⟶ P ↦ z x) hd
  change ((d x : K) : P) = x at hx
  rw [← hx]
  exact (d x).property

/-- 片方の環の生成元の像は pushout でも他方の環上の生成元になる。 -/
theorem closure_image_generators_eq_top_of_isPushout
    {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (h : IsPushout f g i j)
    (s : Set C) (hs : Subring.closure (Set.range g ∪ s) = ⊤) :
    Subring.closure (Set.range i ∪ j '' s) = ⊤ := by
  let K := Subring.closure (Set.range i ∪ j '' s)
  have hj : ∀ x : C, j x ∈ K := by
    have ht : (⊤ : Subring C) ≤ K.comap j.hom := by
      rw [← hs]
      apply Subring.closure_le.mpr
      rintro x (⟨a, rfl⟩ | hx)
      · change j (g a) ∈ K
        rw [← show i (f a) = j (g a) from congrArg (fun z : A ⟶ P ↦ z a) h.w]
        exact Subring.subset_closure (.inl ⟨f a, rfl⟩)
      · exact Subring.subset_closure (.inr ⟨x, hx, rfl⟩)
    exact fun x ↦ ht (Subring.mem_top x)
  apply top_unique
  rw [← closure_range_union_eq_top_of_isPushout h]
  apply Subring.closure_le.mpr
  rintro x (⟨b, rfl⟩ | ⟨c, rfl⟩)
  · exact Subring.subset_closure (.inl ⟨b, rfl⟩)
  · exact hj c

end SerrePositivity.AlgebraicGeometry

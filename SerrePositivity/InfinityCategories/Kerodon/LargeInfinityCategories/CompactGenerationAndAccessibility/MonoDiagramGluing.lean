module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ChainGluing

/-!
概要：元の単射形状の整合族を、同じ全単体の合併上の射へ貼り合わせる。
方針：各単射の像と厳密な像同型へ移し、増大部分複体の貼り合わせを使う。
規約：元の形状と各段への制限を厳密な等式で回収する。
使われ方：各閉前置形状の全図式から極限前置図式を組み立てる。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：全単体を覆う単射形状の増大族上の整合する射は、一つの全射に貼り合わさる。
方針：像の部分複体に移して貼り、元の形状との同型を消去する。
規約：形状の遷移射と被覆写像の元の等式を使う。
使われ方：well-founded 相対交互構成の極限段の全前置図式。 -/
lemma exists_compatibleMonoGluing {I : Type v} [LinearOrder I]
    {X Y : SSet.{u}} (A : I → SSet.{u}) (f : ∀ i, A i ⟶ X) [∀ i, Mono (f i)]
    (g : ∀ i j, i ≤ j → (A i ⟶ A j))
    (hgf : ∀ i j (h : i ≤ j), g i j h ≫ f j = f i)
    (hcover : ∀ n (x : X.obj n), ∃ i, ∃ y : (A i).obj n, (f i).app n y = x)
    (F : ∀ i, A i ⟶ Y)
    (hF : ∀ i j (h : i ≤ j), g i j h ≫ F j = F i) :
    ∃ G : X ⟶ Y, ∀ i, f i ≫ G = F i := by
  let R := fun i ↦ Subcomplex.range (f i)
  let t := fun i ↦ asIso (Subfunctor.toRange (f i))
  have hR : Monotone R := by
    intro i j hij n x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(g i j hij).app n y,
      congrArg (fun z ↦ z.app n y) (hgf i j hij)⟩
  have hc : ∀ n (x : X.obj n), ∃ i, x ∈ (R i).obj n := by
    intro n x
    obtain ⟨i, y, hy⟩ := hcover n x
    exact ⟨i, y, hy⟩
  let H := fun i ↦ (t i).inv ≫ F i
  have hH : ∀ i j (h : i ≤ j), Subcomplex.homOfLE (hR h) ≫ H j = H i := by
    intro i j hij
    have ht : (t i).hom ≫ Subcomplex.homOfLE (hR hij) = g i j hij ≫ (t j).hom := by
      apply (cancel_mono (R j).ι).1
      rw [Category.assoc, Subcomplex.homOfLE_ι]
      change Subfunctor.toRange (f i) ≫ (Subcomplex.range (f i)).ι =
        (g i j hij ≫ Subfunctor.toRange (f j)) ≫ (Subcomplex.range (f j)).ι
      rw [Subfunctor.toRange_ι, Category.assoc, Subfunctor.toRange_ι, hgf i j hij]
    apply (cancel_epi (t i).hom).1
    dsimp only [H]
    rw [← Category.assoc, ht, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id_assoc, hF i j hij]
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_chainGluing R hR hc H hH
  refine ⟨G, fun i ↦ ?_⟩
  calc
    _ = ((t i).hom ≫ (R i).ι) ≫ G := rfl
    _ = F i := by
      rw [Category.assoc, hG]
      dsimp only [H]
      rw [Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

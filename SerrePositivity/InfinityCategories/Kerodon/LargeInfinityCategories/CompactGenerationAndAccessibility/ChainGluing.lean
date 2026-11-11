module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SmallPieceChains

/-!
概要：増大する全前置部分複体上の整合する射を、同じ合併上の全射へ貼り合わせる。
方針：各単体を含む段を選び、共通の上段で選択の独立性と自然性を示す。
規約：各段との等式は全単体上で厳密に保持する。
使われ方：長さ κ₀ の相対構成の極限段と最終段。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

private lemma chainValue_eq {I : Type v} [LinearOrder I] {X Y : SSet.{u}}
    (A : I → X.Subcomplex) (hA : Monotone A)
    (F : ∀ i, (A i : SSet.{u}) ⟶ Y)
    (hF : ∀ i j (h : i ≤ j), (Subcomplex.homOfLE (hA h)) ≫ F j = F i)
    (i j : I) (n : SimplexCategoryᵒᵖ) (x : X.obj n)
    (hi : x ∈ (A i).obj n) (hj : x ∈ (A j).obj n) :
    (F i).app n ⟨x, hi⟩ = (F j).app n ⟨x, hj⟩ := by
  have h₁ := congrArg (fun f ↦ f.app n ⟨x, hi⟩) (hF i (max i j) (le_max_left _ _))
  have h₂ := congrArg (fun f ↦ f.app n ⟨x, hj⟩) (hF j (max i j) (le_max_right _ _))
  exact h₁.symm.trans h₂

/-- 概要：全単体を覆う増大部分複体の整合族は、一つの元の全射に貼り合わさる。
方針：単体ごとの段を選び、二段の最大で値を比較する。
規約：自然性を全単体写像について証明し、各前置段を厳密に回収する。
使われ方：相対交互構成の全前置図式と増大余錐の同時貼り合わせ。 -/
lemma exists_chainGluing {I : Type v} [LinearOrder I] {X Y : SSet.{u}}
    (A : I → X.Subcomplex) (hA : Monotone A)
    (hcover : ∀ n (x : X.obj n), ∃ i, x ∈ (A i).obj n)
    (F : ∀ i, (A i : SSet.{u}) ⟶ Y)
    (hF : ∀ i j (h : i ≤ j), (Subcomplex.homOfLE (hA h)) ≫ F j = F i) :
    ∃ G : X ⟶ Y, ∀ i, (A i).ι ≫ G = F i := by
  let t := fun n x ↦ Classical.choose (hcover n x)
  have ht : ∀ n x, x ∈ (A (t n x)).obj n := fun n x ↦ Classical.choose_spec (hcover n x)
  let G : X ⟶ Y :=
    { app := fun n ↦ ↾fun x ↦ (F (t n x)).app n ⟨x, ht n x⟩
      naturality := by
        intro n m f
        apply ConcreteCategory.hom_ext
        intro x
        change (F (t m (X.map f x))).app m ⟨X.map f x, ht _ _⟩ =
          Y.map f ((F (t n x)).app n ⟨x, ht _ _⟩)
        have hnat := congrArg (fun g ↦ g ⟨x, ht n x⟩) ((F (t n x)).naturality f)
        change (F (t n x)).app m ⟨X.map f x, (A (t n x)).map f (ht n x)⟩ =
          Y.map f ((F (t n x)).app n ⟨x, ht n x⟩) at hnat
        exact (chainValue_eq A hA F hF _ _ m (X.map f x) (ht _ _)
          ((A (t n x)).map f (ht n x))).trans hnat }
  refine ⟨G, fun i ↦ ?_⟩
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact chainValue_eq A hA F hF _ i n x.val (ht n x.val) x.property

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

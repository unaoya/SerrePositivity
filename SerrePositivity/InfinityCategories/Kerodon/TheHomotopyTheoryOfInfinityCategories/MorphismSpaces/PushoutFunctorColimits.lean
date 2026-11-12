module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：点ごとの pushout で作った関手の余極限の保存。
方針：pushout と余極限の可換性を各余極限の錐に適用する。
規約：モデル構造を使わない通常の圏論の補題。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の join と写像円柱のセル分解への接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
universe u v
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：点ごとの pushout の三つの関手が余極限を保てば第四も保つ。
方針：余極限の cocone の点での pushout に、pushout と余極限の可換性を適用する。
規約：固定した形 J の余極限だけを要求する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の二段の貼り合わせ関手。 -/
lemma preservesColimitsOfShape_of_pointwise_pushout
    {C : Type u} [Category C] {D : Type v} [Category D] [HasPushouts D]
    (J : Type*) [Category* J] {F₁ F₂ F₃ F₄ : C ⥤ D}
    (t : F₁ ⟶ F₂) (l : F₁ ⟶ F₃) (r : F₂ ⟶ F₄) (b : F₃ ⟶ F₄)
    (h : ∀ X, IsPushout (t.app X) (l.app X) (r.app X) (b.app X))
    [PreservesColimitsOfShape J F₁] [PreservesColimitsOfShape J F₂]
    [PreservesColimitsOfShape J F₃] : PreservesColimitsOfShape J F₄ := by
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
  have sq : IsPushout (Functor.whiskerLeft F t) (Functor.whiskerLeft F l)
      (Functor.whiskerLeft F r) (Functor.whiskerLeft F b) :=
    IsPushout.of_forall_isPushout_app (fun j ↦ h (F.obj j))
  exact sq.isColimitOfIsColimitOfIsPushout
    (F₁.mapCocone c) (F₂.mapCocone c) (F₃.mapCocone c) (F₄.mapCocone c)
    (isColimitOfPreserves F₁ hc) (isColimitOfPreserves F₂ hc) (isColimitOfPreserves F₃ hc)
    (h c.pt) (fun j ↦ t.naturality (c.ι.app j)) (fun j ↦ l.naturality (c.ι.app j))
    (fun j ↦ r.naturality (c.ι.app j)) (fun j ↦ b.naturality (c.ι.app j))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

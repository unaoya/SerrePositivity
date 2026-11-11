module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingTower

/-!
概要：整合した全相対塔の成分表示添字を元の全序数上へ貼り合わせる。
方針：全成分単体を最後の頂点の閉成分段へ持ち上げる。
規約：同じ表示添字圏に値を取る全射を構成する。
使われ方：最終交互図式の両成分を元の表示内の図式として読む。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：閉成分前置形状の元の全序数への包含。
方針：部分型の値を忘却する順序関手。
規約：元の各頂点を保持する。
使われ方：全成分表示の前置制限。 -/
def componentClosedInclusion (κ : Cardinal.{u}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ a c ⥤ κ.ord.ToType :=
  (⟨Subtype.val, fun _ _ h ↦ h⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ a c →o κ.ord.ToType).toFunctor

private def boundedComponentSimplex (κ : Cardinal.{u}) (c : Fin 2) {n : ℕ}
    (s : ComposableArrows κ.ord.ToType n) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ (toLex (s.obj (Fin.last n), c)) c) n where
  obj i := ⟨s.obj i, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.sameComponent_le κ _ _ c).2
    (leOfHom (s.map (homOfLE (Fin.le_last i))))⟩
  map f := homOfLE (leOfHom (s.map f))

/-- 概要：全閉成分前置段は元の全序数 nerve の全単体を覆う。
方針：各単体を最後の頂点の同じ成分位置で持ち上げる。
規約：全単体を厳密に回収する。
使われ方：成分表示の全塔貼り合わせ。 -/
lemma componentClosedInclusion_cover (κ : Cardinal.{u}) (c : Fin 2)
    (n : SimplexCategoryᵒᵖ) (s : (nerve κ.ord.ToType).obj n) :
    ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ,
      ∃ t : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ a c)).obj n,
        (nerveMap (componentClosedInclusion κ a c)).app n t = s := by
  refine ⟨toLex (s.obj (Fin.last n.unop.len), c), boundedComponentSimplex κ c s, ?_⟩
  exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：全閉成分段上で整合した表示添字は全序数上に貼り合わさる。
方針：同じ全単体被覆と単射族の貼り合わせを使う。
規約：元の各前置制限を厳密に保持する。
使われ方：最終交互図式を元の二つの表示内で構成する。 -/
lemma exists_componentTowerGluing (κ : Cardinal.{u}) (c : Fin 2) {Y : SSet.{u}}
    (F : ∀ a, nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ a c) ⟶ Y)
    (hF : ∀ a b (h : a ≤ b),
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentClosedMap h c) ≫ F b = F a) :
    ∃ G : nerve κ.ord.ToType ⟶ Y, ∀ a,
      nerveMap (componentClosedInclusion κ a c) ≫ G = F a := by
  let A := fun a ↦ nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ a c)
  let f := fun a ↦ nerveMap (componentClosedInclusion κ a c)
  let g := fun (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (h : a ≤ b) ↦
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentClosedMap h c)
  have : ∀ a, Mono (f a) := by
    intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.nerveMap_mono_of_thin_obj_injective _ Subtype.val_injective
  have hgf : ∀ a b (h : a ≤ b), g a b h ≫ f b = f a := by intros; rfl
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compatibleMonoGluing A f g hgf (componentClosedInclusion_cover κ c) F hF

/-- 概要：持ち上げた全成分図式の等式を全閉前置段への制限で判定する。
方針：全単体被覆を ULift の元へ適用する。
規約：全射の厳密な等式。
使われ方：貼り合わせた全交互図式と元の成分表示の整合。 -/
lemma componentTower_ulift_hom_ext (κ : Cardinal.{u}) (c : Fin 2) {Y : SSet.{max u v}}
    {F G : (SSet.uliftFunctor.{v, u}).obj (nerve κ.ord.ToType) ⟶ Y}
    (h : ∀ a, (SSet.uliftFunctor.{v, u}).map
        (nerveMap (componentClosedInclusion κ a c)) ≫ F =
      (SSet.uliftFunctor.{v, u}).map
        (nerveMap (componentClosedInclusion κ a c)) ≫ G) : F = G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  obtain ⟨a, t, rfl⟩ := componentClosedInclusion_cover κ c n s
  exact congrArg (fun f ↦ f.app n (ULift.up t)) (h a)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

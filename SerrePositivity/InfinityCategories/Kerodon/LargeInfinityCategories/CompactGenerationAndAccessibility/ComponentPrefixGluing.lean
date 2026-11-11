module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.OrdinalPrefixes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.MonoDiagramGluing

/-!
概要：全過去段の元の成分表示添字を、極限前置段へ厳密に貼り合わせる。
方針：各成分単体を最後の頂点の交互段へ持ち上げ、全単体被覆を使う。
規約：全交互段と成分の長さを変更せず、元の表示添字を保持する。
使われ方：相対交互構成の各再帰段の両成分の全表示図式。

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

/-- 概要：過去の閉成分前置形状を現在の厳密成分前置形状へ含める。
方針：同じ段の上界の推移性を記録する。
規約：元の成分を変更しない。
使われ方：過去の全成分表示添字の制限。 -/
def componentClosedIntoLower {κ : Cardinal.{u}} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)
    (b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}) (c : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ b.val c ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c :=
  (⟨fun i ↦ ⟨i.val, i.property.trans_lt b.property⟩, fun _ _ h ↦ h⟩ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ b.val c →o _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c).toFunctor

private def componentBoundedSimplex (κ : Cardinal.{u}) (c : Fin 2) {n : ℕ}
    (s : ComposableArrows κ.ord.ToType n) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ (toLex (s.obj (Fin.last n), c)) c) n where
  obj i := ⟨s.obj i, leOfHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingSection κ c).map
    (homOfLE (leOfHom (s.map (homOfLE (Fin.le_last i))))))⟩
  map f := homOfLE (leOfHom (s.map f))

/-- 概要：過去の閉成分形状は現在の厳密成分形状の全単体を覆う。
方針：各単体の最後の成分段を過去段として選ぶ。
規約：全単体を元の閉前置形状から厳密に回収する。
使われ方：成分表示添字の極限貼り合わせと射の等号判定。 -/
lemma componentClosedIntoLower_cover {κ : Cardinal.{u}} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2)
    (n : SimplexCategoryᵒᵖ) (s : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c)).obj n) :
    ∃ b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a},
      ∃ t : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ b.val c)).obj n,
        (nerveMap (componentClosedIntoLower a b c)).app n t = s := by
  let U : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c ⥤ κ.ord.ToType :=
    (⟨Subtype.val, fun _ _ h ↦ h⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c →o κ.ord.ToType).toFunctor
  let s' := s ⋙ U
  refine ⟨⟨toLex ((s.obj (Fin.last n.unop.len)).val, c),
    (s.obj (Fin.last n.unop.len)).property⟩, componentBoundedSimplex κ c s', ?_⟩
  exact ComposableArrows.ext (fun _ ↦ Subtype.ext rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：整合する過去の全成分表示は現在の厳密成分前置形状へ貼り合わさる。
方針：最後の成分段による全単体被覆と単射族の貼り合わせを使う。
規約：元の表示添字に値を取る同じ全射を構成する。
使われ方：極限段を含む各再帰段の元の成分表示添字。 -/
lemma exists_componentPrefixGluing {κ : Cardinal.{u}} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2)
    {Y : SSet.{u}}
    (F : ∀ b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a},
      nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ b.val c) ⟶ Y)
    (hF : ∀ b d (h : b ≤ d),
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentClosedMap (a := b.val) (b := d.val) h c) ≫ F d = F b) :
    ∃ G : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c) ⟶ Y, ∀ b,
      nerveMap (componentClosedIntoLower a b c) ≫ G = F b := by
  let A := fun b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a} ↦
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ b.val c)
  let f := fun b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a} ↦
    nerveMap (componentClosedIntoLower a b c)
  let g := fun (b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}) (h : b ≤ d) ↦
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentClosedMap (a := b.val) (b := d.val) h c)
  have : ∀ b, Mono (f b) := by
    intro b
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.nerveMap_mono_of_thin_obj_injective
    intro i j h
    apply Subtype.ext
    exact congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c ↦ x.val) h
  have hgf : ∀ b d (h : b ≤ d), g b d h ≫ f d = f b := by
    intro b d h
    rfl
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compatibleMonoGluing A f g hgf (componentClosedIntoLower_cover a c) F hF

/-- 概要：全過去成分への制限が一致する二つの射は全厳密前置形状上で一致する。
方針：最後の成分段による全単体被覆で比較する。
規約：全単体上の等式を結論する。
使われ方：貼り合わせた全交互図式と元の成分表示図式の厳密な一致。 -/
lemma componentPrefix_hom_ext {κ : Cardinal.{u}} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2)
    {Y : SSet.{u}} {F G : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c) ⟶ Y}
    (h : ∀ b, nerveMap (componentClosedIntoLower a b c) ≫ F =
      nerveMap (componentClosedIntoLower a b c) ≫ G) : F = G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨b, t, rfl⟩ := componentClosedIntoLower_cover a c n s
  exact congrArg (fun f ↦ f.app n t) (h b)

/-- 概要：宇宙を持ち上げた全成分図式の一致も、全過去段への制限で判定できる。
方針：同じ全単体被覆を ULift の元へ適用する。
規約：元の成分形状と宇宙持ち上げを保持する。
使われ方：固定標的 slice 内の全図式の成分整合。 -/
lemma componentPrefix_ulift_hom_ext {κ : Cardinal.{u}} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2)
    {Y : SSet.{max u v}}
    {F G : (SSet.uliftFunctor.{v, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c)) ⟶ Y}
    (h : ∀ b, (SSet.uliftFunctor.{v, u}).map (nerveMap (componentClosedIntoLower a b c)) ≫ F =
      (SSet.uliftFunctor.{v, u}).map (nerveMap (componentClosedIntoLower a b c)) ≫ G) : F = G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  obtain ⟨b, t, rfl⟩ := componentClosedIntoLower_cover a c n s
  exact congrArg (fun f ↦ f.app n (ULift.up t)) (h b)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

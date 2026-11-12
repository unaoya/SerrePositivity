module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.OrdinalPrefixes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.MonoDiagramGluing

/-!
概要：閉前置順序の全図式族を、元の全順序 nerve 上に貼り合わせる。
方針：各単体を最後の頂点以下の形状へ持ち上げ、元の単射族の貼り合わせを使う。
規約：宇宙を持ち上げた元の全単体と各前置制限の厳密な等式を保持する。
使われ方：well-founded 再帰で得た全前置段から最終交互図式を作る。

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

/-- 概要：閉前置順序の元の順序への包含。
方針：部分型の忘却を順序関手にする。
規約：元の順序射を使う。
使われ方：全交互図式の前置制限。 -/
def closedPrefixInclusion {I : Type u} [Preorder I] (a : I) : {i : I // i ≤ a} ⥤ I :=
  (⟨Subtype.val, fun _ _ h ↦ h⟩ : {i : I // i ≤ a} →o I).toFunctor

/-- 概要：二つの閉前置順序の包含。
方針：上界の推移性を部分型に記録する。
規約：同じ元の点を保持する。
使われ方：全前置段の厳密な整合条件。 -/
def closedPrefixMap {I : Type u} [Preorder I] {a b : I} (h : a ≤ b) :
    {i : I // i ≤ a} ⥤ {i : I // i ≤ b} :=
  (⟨fun i ↦ ⟨i.val, i.property.trans h⟩, fun _ _ hij ↦ hij⟩ :
    {i : I // i ≤ a} →o {i : I // i ≤ b}).toFunctor

private def closedPrefixSimplex {I : Type u} [Preorder I] {n : ℕ}
    (s : ComposableArrows I n) :
    ComposableArrows {i : I // i ≤ s.obj (Fin.last n)} n where
  obj i := ⟨s.obj i, leOfHom (s.map (homOfLE (Fin.le_last i)))⟩
  map f := homOfLE (leOfHom (s.map f))

private lemma closedPrefixSimplex_projection {I : Type u} [Preorder I] {n : ℕ}
    (s : ComposableArrows I n) :
    (nerveMap (closedPrefixInclusion (s.obj (Fin.last n)))).app
      (Opposite.op ⦋n⦌) (closedPrefixSimplex s) = s :=
  ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：整合する全閉前置図式は、元の全順序 nerve 上の一つの図式に貼り合わさる。
方針：各単体を最後の頂点の閉前置段へ持ち上げて全単体被覆を得る。
規約：元の小さい形状の宇宙持ち上げを使用する。
使われ方：全相対交互塔から最終図式と全前置制限を回収する。 -/
lemma exists_closedPrefixGluing {I : Type u} [LinearOrder I]
    {Y : SSet.{max u v}}
    (F : ∀ a : I, (SSet.uliftFunctor.{v, u}).obj (nerve {i : I // i ≤ a}) ⟶ Y)
    (hF : ∀ a b (h : a ≤ b),
      (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixMap h)) ≫ F b = F a) :
    ∃ G : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ Y, ∀ a,
      (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixInclusion a)) ≫ G = F a := by
  let A := fun a : I ↦ (SSet.uliftFunctor.{v, u}).obj (nerve {i : I // i ≤ a})
  let f := fun a : I ↦ (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixInclusion a))
  let g := fun (a b : I) (h : a ≤ b) ↦ (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixMap h))
  have hm (a : I) : Mono (nerveMap (closedPrefixInclusion a)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.nerveMap_mono_of_thin_obj_injective (closedPrefixInclusion a) Subtype.val_injective
  have : ∀ a, Mono (f a) := by
    intro a
    rw [NatTrans.mono_iff_mono_app]
    intro n
    apply (mono_iff_injective _).2
    rintro ⟨x⟩ ⟨y⟩ h
    apply ULift.ext
    have : Mono ((nerveMap (closedPrefixInclusion a)).app n) :=
      (NatTrans.mono_iff_mono_app _).mp (hm a) n
    exact (mono_iff_injective _).mp this (congrArg ULift.down h)
  have hgf : ∀ a b (h : a ≤ b), g a b h ≫ f b = f a := by
    intro a b h
    rfl
  have hc : ∀ n (x : ((SSet.uliftFunctor.{v, u}).obj (nerve I)).obj n),
      ∃ a, ∃ y : (A a).obj n, (f a).app n y = x := by
    rintro n ⟨s⟩
    refine ⟨s.obj (Fin.last n.unop.len), ULift.up (closedPrefixSimplex s), ?_⟩
    apply ULift.ext
    exact closedPrefixSimplex_projection s
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compatibleMonoGluing A f g hgf hc F hF

/-- 概要：厳密前置順序の元の順序への包含。
方針：部分型の忘却を順序関手にする。
規約：元の順序射を保持する。
使われ方：極限前置段の単体を元の順序で比較する。 -/
def strictPrefixInclusion {I : Type u} [Preorder I] (a : I) : {i : I // i < a} ⥤ I :=
  (⟨Subtype.val, fun _ _ h ↦ h⟩ : {i : I // i < a} →o I).toFunctor

/-- 概要：過去の閉前置形状を、指定した厳密前置形状へ含める。
方針：上界の推移性で同じ点を送る。
規約：元の各頂点を保持する。
使われ方：全過去段から極限前置段への制限。 -/
def closedPrefixIntoStrict {I : Type u} [Preorder I] (a : I) (b : {i : I // i < a}) :
    {i : I // i ≤ b.val} ⥤ {i : I // i < a} :=
  (⟨fun i ↦ ⟨i.val, i.property.trans_lt b.property⟩, fun _ _ h ↦ h⟩ :
    {i : I // i ≤ b.val} →o {i : I // i < a}).toFunctor

/-- 概要：全過去の閉前置図式は、極限段を含む厳密前置形状へ貼り合わさる。
方針：各単体を最後の頂点の閉前置段へ持ち上げ、単射族の貼り合わせを使う。
規約：前置形状に終頂点を要求しない。
使われ方：well-founded 相対交互構成の各再帰段の全前置図式。 -/
lemma exists_strictPrefixGluing {I : Type u} [LinearOrder I] (a : I)
    {Y : SSet.{max u v}}
    (F : ∀ b : {i : I // i < a},
      (SSet.uliftFunctor.{v, u}).obj (nerve {i : I // i ≤ b.val}) ⟶ Y)
    (hF : ∀ b c (h : b ≤ c),
      (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixMap (I := I) (a := b.val) (b := c.val) h)) ≫ F c = F b) :
    ∃ G : (SSet.uliftFunctor.{v, u}).obj (nerve {i : I // i < a}) ⟶ Y, ∀ b,
      (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixIntoStrict a b)) ≫ G = F b := by
  let A := fun b : {i : I // i < a} ↦
    (SSet.uliftFunctor.{v, u}).obj (nerve {i : I // i ≤ b.val})
  let f := fun b : {i : I // i < a} ↦
    (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixIntoStrict a b))
  let g := fun (b c : {i : I // i < a}) (h : b ≤ c) ↦
    (SSet.uliftFunctor.{v, u}).map (nerveMap (closedPrefixMap (I := I) (a := b.val) (b := c.val) h))
  have hm (b : {i : I // i < a}) : Mono (nerveMap (closedPrefixIntoStrict a b)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.nerveMap_mono_of_thin_obj_injective
    intro i j h
    apply Subtype.ext
    exact congrArg (fun x : {i : I // i < a} ↦ x.val) h
  have : ∀ b, Mono (f b) := by
    intro b
    rw [NatTrans.mono_iff_mono_app]
    intro n
    apply (mono_iff_injective _).2
    rintro ⟨x⟩ ⟨y⟩ h
    apply ULift.ext
    have : Mono ((nerveMap (closedPrefixIntoStrict a b)).app n) :=
      (NatTrans.mono_iff_mono_app _).mp (hm b) n
    exact (mono_iff_injective _).mp this (congrArg ULift.down h)
  have hgf : ∀ b c (h : b ≤ c), g b c h ≫ f c = f b := by
    intro b c h
    rfl
  have hc : ∀ n (x : ((SSet.uliftFunctor.{v, u}).obj (nerve {i : I // i < a})).obj n),
      ∃ b, ∃ y : (A b).obj n, (f b).app n y = x := by
    rintro n ⟨s⟩
    let s' := s ⋙ strictPrefixInclusion a
    refine ⟨s.obj (Fin.last n.unop.len), ULift.up (closedPrefixSimplex s'), ?_⟩
    apply ULift.ext
    exact ComposableArrows.ext (fun _ ↦ Subtype.ext rfl) (fun _ _ ↦ Subsingleton.elim _ _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compatibleMonoGluing A f g hgf hc F hF

/-- 概要：厳密前置順序を同じ閉前置順序へ含める。
方針：厳密な上界を弱い上界へ忘却する。
規約：元の各点を保持する。
使われ方：一頂点追加後の元の全前置段への制限。 -/
def strictPrefixToClosed {I : Type u} [Preorder I] (a : I) :
    {i : I // i < a} ⥤ {i : I // i ≤ a} :=
  (⟨fun i ↦ ⟨i.val, i.property.le⟩, fun _ _ h ↦ h⟩ :
    {i : I // i < a} →o {i : I // i ≤ a}).toFunctor

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

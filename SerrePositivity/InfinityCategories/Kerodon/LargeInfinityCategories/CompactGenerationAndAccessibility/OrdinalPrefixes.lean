module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.OrdinalCompactColimits
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.PosetLowerJoinIso

/-!
概要：長さ κ₀ の交互順序の全前置形状と、各成分の元の包含を固定する。
方針：厳密下方集合と各成分の逆像を取り、nerve の単射性と μ-small 性を示す。
規約：極限前置段にも終頂点を要求しない。
使われ方：全前置図式を保持する相対因子化と一頂点追加の形状比較。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：交互順序の指定段より前の元の全順序。
方針：厳密下方集合を部分型として保持する。
規約：後続段と極限段を同じ定義で扱う。
使われ方：相対交互構成の全前置図式の添字。 -/
abbrev AlternatingLower (κ : Cardinal.{u}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) :=
  {b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // b < a}

/-- 概要：指定成分のうち全前置図式に属する元の段。
方針：固定成分包含による厳密下方集合の逆像を取る。
規約：元の κ 順序の段を変更しない。
使われ方：同じ表示添字へ写す既存成分の全前置図式。 -/
abbrev AlternatingComponentLower (κ : Cardinal.{u}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) :=
  {b : κ.ord.ToType // toLex (b, c) < a}

/-- 概要：指定成分の全前置段を全交互前置段へ含める関手。
方針：固定成分の辞書式順序への単調性を制限する。
規約：元の順序と全射を保持する。
使われ方：相対因子化で厳密に固定する部分図式の包含。 -/
def alternatingLowerSection (κ : Cardinal.{u}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) :
    AlternatingComponentLower κ a c ⥤ AlternatingLower κ a :=
  (show Monotone (fun b : AlternatingComponentLower κ a c ↦
      (⟨toLex (b.val, c), b.property⟩ : AlternatingLower κ a)) from by
    intro b d hbd
    exact Prod.Lex.toLex_le_toLex.mpr
      ((show b.val ≤ d.val from hbd).lt_or_eq.elim Or.inl
        (fun h ↦ Or.inr ⟨h, le_rfl⟩))).functor

/-- 概要：thin 圏の対象上単射な関手の nerve は全単体上で単射。
方針：全単体の各頂点を比較し、thin 性で全射の一致を得る。
規約：元の関手と nerve を変更しない。
使われ方：前置形状と各成分の包含の単射性。 -/
lemma nerveMap_mono_of_thin_obj_injective
    {I J : Type u} [SmallCategory I] [SmallCategory J] [Quiver.IsThin I]
    (F : I ⥤ J) (hF : Function.Injective F.obj) : Mono (nerveMap F) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  intro s t h
  exact ComposableArrows.ext
    (fun i ↦ hF (congrArg (fun z ↦ z.obj i) h))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：既存成分の全前置図式の包含は全単体上で単射。
方針：元の段の単射性を thin 圏の nerve に移す。
規約：零単体だけの単射では終えない。
使われ方：全余錐制限の left fibration に要求される単射性。 -/
instance alternatingLowerSection_nerve_mono (κ : Cardinal.{u})
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) : Mono (nerveMap (alternatingLowerSection κ a c)) := by
  apply nerveMap_mono_of_thin_obj_injective
  intro b d h
  apply Subtype.ext
  have h' := congrArg (fun x : AlternatingLower κ a ↦ (ofLex x.val).1) h
  exact h'

/-- 概要：全交互前置段の nerve は同じ μ より小さい。
方針：元の全交互順序の小ささを部分型へ制限する。
規約：極限前置形状の全非退化単体を数える。
使われ方：全前置図式の compact 因子化。 -/
lemma alternatingLower_isKappaSmall {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve (AlternatingLower κ a)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_nerve_of_cardinalChangeBound h _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingIndex_hasCardinalLT h.1).of_injective Subtype.val Subtype.val_injective)

/-- 概要：指定成分の全前置段の nerve も同じ μ より小さい。
方針：元の κ 順序の部分型の小ささを nerve に移す。
規約：有限性や終対象を要求しない。
使われ方：表示添字の前置 coslice の filtered 性。 -/
lemma alternatingComponentLower_isKappaSmall {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve (AlternatingComponentLower κ a c)) := by
  have hκ : HasCardinalLT κ.ord.ToType μ := by
    simpa [hasCardinalLT_iff_cardinal_mk_lt] using h.1
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_nerve_of_cardinalChangeBound h _
    (hκ.of_injective Subtype.val Subtype.val_injective)

/-- 概要：指定成分のうち指定段以下の全前置段。
方針：固定成分包含で弱下方集合を引き戻す。
規約：追加した頂点を含む閉前置形状。
使われ方：再帰で選ぶ各全段の成分表示添字。 -/
abbrev AlternatingComponentClosed (κ : Cardinal.{u}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) :=
  {b : κ.ord.ToType // toLex (b, c) ≤ a}

/-- 概要：各成分の閉前置形状を全交互閉前置形状へ含める。
方針：元の固定成分の単調性を部分型へ制限する。
規約：元の各頂点と全順射を保持する。
使われ方：閉前置段の元の成分図式との厳密な比較。 -/
def alternatingClosedSection (κ : Cardinal.{u}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) :
    AlternatingComponentClosed κ a c ⥤ {b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // b ≤ a} :=
  (show Monotone (fun b : AlternatingComponentClosed κ a c ↦
      (⟨toLex (b.val, c), b.property⟩ : {b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // b ≤ a})) from by
    intro b d hbd
    exact leOfHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingSection κ c).map (homOfLE hbd))).functor

/-- 概要：成分の閉前置段を後の閉前置段へ含める。
方針：同じ点の上界の推移性を記録する。
規約：成分を変更しない。
使われ方：全過去の成分表示添字の厳密な整合条件。 -/
def alternatingComponentClosedMap {κ : Cardinal.{u}} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ}
    (h : a ≤ b) (c : Fin 2) :
    AlternatingComponentClosed κ a c ⥤ AlternatingComponentClosed κ b c :=
  (⟨fun i ↦ ⟨i.val, i.property.trans h⟩, fun _ _ h' ↦ h'⟩ :
    AlternatingComponentClosed κ a c →o AlternatingComponentClosed κ b c).toFunctor

/-- 概要：閉前置成分の包含は全 nerve 上で単射。
方針：元の段の単射性を thin nerve の判定へ渡す。
規約：元の高次単体を保持する。
使われ方：閉前置余錐を固定する制限の単射性。 -/
instance alternatingClosedSection_nerve_mono (κ : Cardinal.{u})
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) : Mono (nerveMap (alternatingClosedSection κ a c)) := by
  apply nerveMap_mono_of_thin_obj_injective
  intro b d h
  apply Subtype.ext
  exact congrArg (fun x : {b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // b ≤ a} ↦ (ofLex x.val).1) h

/-- 概要：同じ成分の厳密前置形状を閉前置形状へ含める。
方針：厳密な上界を弱い上界へ忘却する。
規約：元の各順序段を保持する。
使われ方：一頂点追加の元の成分への制限。 -/
def alternatingComponentLowerToClosed (κ : Cardinal.{u}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (c : Fin 2) :
    AlternatingComponentLower κ a c ⥤ AlternatingComponentClosed κ a c :=
  (⟨fun i ↦ ⟨i.val, i.property.le⟩, fun _ _ h ↦ h⟩ :
    AlternatingComponentLower κ a c →o AlternatingComponentClosed κ a c).toFunctor

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedStrictConeFamily
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：始対象付き図式上の weighted な strict 錐の比較を元の図式へ制限する。
方針：展開した族の単体を比較し、元の対象上の脚が元の錐と一致することを使う。
規約：頂点評価の切断の選択を使わない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の q′ と native な制限の可換性。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：始対象付き図式の coherent 表示は元の図式への包含上で元の表示に一致する。
方針：通常の関手の前合成に関する自然性と元の図式への制限を使う。
規約：全次数の射の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の切断の制限の終域の正規化。 -/
lemma smallStrictConeDiagram_restriction {F : I ⥤ C} (c : Cone F) :
    (SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C := I))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.smallStrictConeFunctor c) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.smallStrictConeFunctor_restriction]

/-- 概要：始対象付き錐の反転した weighted 比較の展開は元の図式への制限と可換。
方針：全パラメータの展開式を使い、単体ごとに元の図式と脚の値を比較する。
規約：Hom の Kan 性や錐の極限性は要求しない。
使われ方：HTT 4.2.4.1 の q′ の制限の可換式の基礎。 -/
lemma smallStrictConeExtension_comparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    ((SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C := I))) ▷
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.smallStrictConeExtension c) x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨σ⟩, ⟨a⟩⟩
  apply Subtype.ext
  rfl

/-- 概要：weighted な錐全体上の族を元の図式へ制限すると元の q′ の切断比較になる。
方針：相対関手の展開で検出し、二つの包含の合成と全パラメータの制限の式を使う。
規約：Kan 性や極限性を仮定しない射の厳密な等式。
使われ方：HTT 4.2.4.1 の豊穣比較と native な極限判定を結ぶ主可換式。 -/
lemma weightedStrictConeFamilyComparison_restriction {F : I ⥤ C} (c : Cone F) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison c x ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_eqToHom _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c).property,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison_uncurry,
    ← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.smallStrictConeParameter_inr,
    smallStrictConeExtension_comparison_uncurry]

variable [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：strict な錐が coherent nerve の極限錐であることは q′ の切断比較の同値性と同値。
方針：native な切断の制限の判定と、weighted な錐全体の比較の同値・主可換式を使う。
規約：添字圏 I と通常の錐 c は任意。追加の比較同値の仮定は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の Hom の homotopy 極限から ∞ 極限への接続。 -/
@[kerodon 03BB]
lemma strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison {F : I ⥤ C}
    (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ x : C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_coneSectionRestriction_homotopyEquivalence]
  constructor
  · intro h x
    rw [← weightedStrictConeFamilyComparison_restriction]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison_homotopyEquivalence c x).comp
      (h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
  · intro h z
    obtain ⟨x, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv C).surjective z
    have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison_homotopyEquivalence c x).isQCatEquivalence
    have hc := (h x).isQCatEquivalence
    rw [← weightedStrictConeFamilyComparison_restriction] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

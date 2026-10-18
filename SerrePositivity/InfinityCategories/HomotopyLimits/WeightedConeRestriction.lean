module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedStrictConeFamily

/-!
概要：始対象付き図式上の weighted な strict 錐の比較を元の図式へ制限する。
方針：展開した族の単体を比較し、元の対象上の脚が元の錐と一致することを使う。
規約：頂点評価の切断の選択を使わない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の q′ と native な制限の可換性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：始対象付き図式の coherent 表示は元の図式への包含上で元の表示に一致する。
方針：通常の関手の前合成に関する自然性と元の図式への制限を使う。
規約：全次数の射の厳密な等式。
使われ方：Kerodon 7.5.4.6 の切断の制限の終域の正規化。 -/
lemma smallStrictConeDiagram_restriction {F : I ⥤ C} (c : Cone F) :
    (SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C := I))) ≫
        strictCoherentDiagram (smallStrictConeFunctor c) = strictCoherentDiagram F := by
  rw [strictCoherentDiagram_precomp, smallStrictConeFunctor_restriction]

/-- 概要：始対象付き錐の反転した weighted 比較の展開は元の図式への制限と可換。
方針：全パラメータの展開式を使い、単体ごとに元の図式と脚の値を比較する。
規約：Hom の Kan 性や錐の極限性は要求しない。
使われ方：HTT 4.2.4.1 の q′ の制限の可換式の基礎。 -/
lemma smallStrictConeExtension_comparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    ((SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C := I))) ▷
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op) ≫
      relativeFunctorUncurry
        (reflectedStrictConeSectionsComparison (smallStrictConeExtension c) x) =
      relativeFunctorUncurry (reflectedStrictConeSectionsComparison c x) := by
  rw [reflectedStrictConeSectionsComparison_uncurry,
    reflectedStrictConeSectionsComparison_uncurry]
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
    weightedStrictConeFamilyComparison c x ≫
        coneSectionRestriction (strictCoherentCone c) (coherentNerveVertex x) =
      reflectedStrictConeSectionsComparison c x := by
  apply relativeFunctorUncurry_injective
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (strictCoherentDiagram F)
  rw [coneSectionRestriction, ← Category.assoc,
    relativeFunctorUncurry_eqToHom _ (strictCoherentCone c).property,
    relativeFunctorUncurry_pre, weightedStrictConeFamilyComparison_uncurry,
    ← Category.assoc, ← comp_whiskerRight, smallStrictConeParameter_inr,
    smallStrictConeExtension_comparison_uncurry]

variable [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：strict な錐が coherent nerve の極限錐であることは q′ の切断比較の同値性と同値。
方針：native な切断の制限の判定と、weighted な錐全体の比較の同値・主可換式を使う。
規約：添字圏 I と通常の錐 c は任意。追加の比較同値の仮定は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の Hom の homotopy 極限から ∞ 極限への接続。 -/
lemma strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x) := by
  rw [isLimitCone_iff_coneSectionRestriction_homotopyEquivalence]
  constructor
  · intro h x
    rw [← weightedStrictConeFamilyComparison_restriction]
    exact (weightedStrictConeFamilyComparison_homotopyEquivalence c x).comp
      (h (coherentNerveVertex x))
  · intro h z
    obtain ⟨x, rfl⟩ := (coherentNerveVertexEquiv C).surjective z
    have hs := (weightedStrictConeFamilyComparison_homotopyEquivalence c x).isQCatEquivalence
    have hc := (h x).isQCatEquivalence
    rw [← weightedStrictConeFamilyComparison_restriction] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits

module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeNativeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy

/-!
概要：coherent な錐の豊穣 Hom の族の持ち上げを、頂点評価を固定して比較する。
方針：頂点評価の trivial Kan fibration に相対ホモトピーの存在を適用する。
規約：比較する族には実際の頂点評価の等式を要求する。終域の一致だけでは判定しない。
使われ方：HTT 4.2.4.1 の coend の比較と native な切断制限の照合。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
  {K : SSet.{max u v}} {p : K ⟶ SimplicialNerve C}

/-- 概要：頂点で同じ族を持ち上げる二つの射は、頂点上で定値なホモトピーで結べる。
方針：任意のパラメータに対して頂点評価の trivial Kan fibration を使う。
規約：パラメータには Kan 性を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の切断の選択に依存しない比較。 -/
lemma coherentConeFamily_homotopy_over_apex (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C)
    {A : SSet.{max u v}}
    (a b : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x) :
    ∃ H : SSet.Homotopy a b,
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x =
        fst A (Δ[1] : SSet.{max u v}) ≫ b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation_trivialKanFibration c z hz x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration _ a b h

/-- 概要：標準の coslice の族を持ち上げる射は、選んだ豊穣 Hom の族とホモトピック。
方針：両者の頂点評価を標準比較へ戻す。
規約：全 Hom パラメータでのホモトピーであり、点ごとの一致だけを仮定しない。
使われ方：HTT 4.2.4.1 の具体的な比較族を native な比較へ置き換える。 -/
lemma reflectedCoherentConeFamilyComparison_homotopy (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C)
    (a : (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x z) :
    Nonempty (SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedCoherentConeFamilyComparison c z hz x) a) := by
  obtain ⟨H, _⟩ := coherentConeFamily_homotopy_over_apex c z hz x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedCoherentConeFamilyComparison c z hz x) a
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedCoherentConeFamilyComparison_evaluation c z hz x).trans ha.symm)
  exact ⟨H⟩

/-- 概要：頂点を正しく持ち上げる任意の族の制限は native な比較と関手同型で結べる。
方針：持ち上げのホモトピーを Kan な切断空間の関手同型にし、実際の制限を後合成する。
規約：指定するのは頂点評価だけであり、錐の極限性は使わない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の coend の比較との整合性の証明。 -/
lemma reflectedCoherentNativeConeComparison_functorIso (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C)
    (a : (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x z) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedCoherentNativeConeComparison c z hz x)
      (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))) := by
  obtain ⟨H⟩ := reflectedCoherentConeFamilyComparison_homotopy c z hz x a ha
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))⟩

/-- 概要：頂点評価を保つ具体的な族の制限が同値なら、元の coherent な錐は極限錐。
方針：族の選択の関手同型不変性と、全頂点での native な極限判定を使う。
規約：比較の始域・終域の一致に加えて、持ち上げと頂点評価の等式を必須とする。
使われ方：HTT 4.2.4.1 の具体的な coend 比較の普遍性への接続。 -/
lemma coherentCone_isLimit_of_family_lifts (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z)
    (a : ∀ x : C, (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
    (ha : ∀ x, a x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeApexEvaluation c z hz x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x z)
    (he : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (a x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCone_isLimit_iff_reflectedNativeComparison c z hz).mpr
  intro x
  obtain ⟨e⟩ := reflectedCoherentNativeConeComparison_functorIso c z hz x (a x) (ha x)
  exact ((he x).isQCatEquivalence.ofFunctorIso e.symm).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

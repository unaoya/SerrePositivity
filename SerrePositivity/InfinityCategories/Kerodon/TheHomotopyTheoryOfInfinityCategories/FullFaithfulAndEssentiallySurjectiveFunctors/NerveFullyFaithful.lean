module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEnrichedNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：局所 Kan な単体的圏の豊穣関手の Hom 上の同値性と coherent nerve の充満忠実性の一致。
方針：coherent Hom 比較の自然性の可換図式に同値の二対三則を適用する。
規約：ホモトピー圏の Hom の全単射だけでなく、全写像空間の同値を使う。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Corollary 5.6.0.6（Tag 028T）、straightening の豊穣 Hom 比較を ∞ 圏へ移す。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：標準頂点へ端点を正規化した coherent Hom 上の射の同値性は、元の豊穣 Hom 上の射の同値性と一致する。
方針：Hom 比較の可換図式と宇宙持ち上げの同値性の反映を使う。
規約：両方の単体的圏の全 Hom は Kan 複体。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、豊穣評価の写像空間の同値性の判定。 -/
lemma coherentPinchedHomMap_isQCatEquivalence_iff
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHomMap F X Y) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (F.map X Y) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence X Y
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence (F.obj X) (F.obj Y)
  constructor
  · intro h
    have hcomp := hc.comp h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_enriched_naturality] at hcomp
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan.{u, v} (F.map X Y)).mp (hd.cancel_right hcomp)
  · intro h
    apply hc.cancel_left
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_enriched_naturality]
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan.{u, v} (F.map X Y)).mpr h).comp hd

/-- 概要：coherent nerve の標準頂点間の実際の写像空間への作用は、豊穣 Hom への作用が同値の場合に限り同値。
方針：正規化した Hom の作用の末尾の同型を二対三則で消去する。
規約：標的の二頂点は coherent nerve の射による像として表示する。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、coherent nerve の充満忠実性の標準頂点での判定。 -/
lemma coherentNerveMap_pinchedHomMap_isQCatEquivalence_iff
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (F.map X Y) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F Y)))).isQCatEquivalence
  have hh := coherentPinchedHomMap_isQCatEquivalence_iff F X Y
  constructor
  · intro h
    exact hh.mp (h.comp he)
  · intro h
    exact he.cancel_right (hh.mpr h)

/-- 概要：豊穣関手の coherent nerve は、全豊穣 Hom に同値を誘導する場合に限り充満忠実。
方針：標準頂点の写像空間の判定を使い、任意の coherent 頂点を元の対象から復元する。
規約：充満忠実性は右 pinched 写像空間の単体的ホモトピー同値性で定義する。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Corollary 5.6.0.6（Tag 028T）、straightening の写像空間の同値を充満忠実性へまとめる。 -/
lemma coherentNerveMap_isFullyFaithful_iff
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)]
    (F : EnrichedFunctor SSet.{u} C D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F) ↔ ∀ X Y : C, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (F.map X Y) := by
  constructor
  · intro h X Y
    exact (coherentNerveMap_pinchedHomMap_isQCatEquivalence_iff F X Y).mp
      (h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)).isQCatEquivalence
  · intro h x y
    have he := (coherentNerveMap_pinchedHomMap_isQCatEquivalence_iff F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).mpr
        (h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y] at he
    exact he.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

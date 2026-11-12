module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedCategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：edgewise な豊穣 Hom の共通解像から元の coherent nerve への同値。
方針：右端射影を豊穣関手にし、各 Hom の trivial Kan fibration と対象の全射性を使う。
規約：同値の構成には元の単体的圏の局所 Kan 性だけを仮定する。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、左右の Hom の比較を一般の coherent な図式へ適用する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：edgewise な豊穣圏から元の単体的圏への右端射影。
方針：各 Hom で重みの右半分への制限を使い、同じ評価点で単位と合成を計算する。
規約：対象は自明な部分型の値を取り出す。
使われ方：Kerodon §8.1.1（Tag 03JF）、共通解像を元の coherent nerve と比較する豊穣関手。 -/
@[kerodon 04F9, kerodon 04FA]
def edgewiseEnrichedRight (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) C where
  obj X := X.val
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom X.val Y.val)
  map_id X := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    rfl
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    rfl

/-- 概要：edgewise な豊穣 Hom の解像から元の coherent nerve への実際の比較射。
方針：右端射影の豊穣関手の coherent nerve を取る。
規約：局所 Kan 性なしで射を定義する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共通解像による coherent な図式の移送。 -/
def edgewiseEnrichedInfinityMap (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) ⟶ SimplicialNerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (edgewiseEnrichedRight C)

/-- 概要：局所 Kan な圏の edgewise な比較射は全ての写像空間で同値を誘導する。
方針：右端射影の trivial Kan fibration 性を coherent nerve の充満忠実性の判定へ適用する。
規約：元の全ての豊穣 Hom の Kan 性を要求する。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、共通解像が高次の Hom を保つこと。 -/
lemma edgewiseEnrichedInfinityMap_isFullyFaithful (C : Type v) [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (edgewiseEnrichedInfinityMap C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff (edgewiseEnrichedRight C)).mpr
  intro X Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom X.val Y.val))

/-- 概要：edgewise な比較射は元の coherent nerve の全ての対象を表す。
方針：任意の頂点から元の対象を取り出し、自明な部分型の同じ対象を選ぶ。
規約：この主張自体は局所 Kan 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共通解像の本質的全射性。 -/
lemma edgewiseEnrichedInfinityMap_isEssentiallySurjective (C : Type v)
    [Category.{u} C] [SimplicialCategory C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (edgewiseEnrichedInfinityMap C) := by
  intro y
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C), ?_⟩
  change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (edgewiseEnrichedRight C)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _)) y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  exact ⟨eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y))⟩

/-- 概要：局所 Kan な単体的圏の edgewise な共通解像は元の coherent nerve と同値。
方針：写像空間の同値と対象の本質的全射性を同値判定に使う。
規約：比較の順方向は右端射影の coherent nerve。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左右の Hom の規約を一般の図式で移送する。 -/
@[kerodon 04FA, kerodon 04FD]
lemma edgewiseEnrichedInfinityMap_isQCatEquivalence (C : Type v) [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (edgewiseEnrichedInfinityMap C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (edgewiseEnrichedInfinityMap_isFullyFaithful C) (edgewiseEnrichedInfinityMap_isEssentiallySurjective C)

/-- 概要：edgewise な共通解像と元の coherent nerve の同値データ。
方針：実際の右端射影の同値性から逆射と両合成の関手同型を選ぶ。
規約：順方向の射は構成済みの比較に固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の coherent な図式を共通解像へ持ち上げる。 -/
noncomputable def edgewiseEnrichedInfinityEquivalence (C : Type v) [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C)) (SimplicialNerve C) :=
  (edgewiseEnrichedInfinityMap_isQCatEquivalence C).choose

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockMapAugmentation
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockMapComparison
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonalComparisonWeak
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonalReductionWeak
public import SerrePositivity.EInfinity.SimplicialLocalization.NerveMap
public import SerrePositivity.EInfinity.SimplicialLocalization.NerveWeakVertexIso
public import SerrePositivity.EInfinity.Hammock.RelativeEquivalenceWeak
public import SerrePositivity.EInfinity.Hammock.ExInfinityWeakMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
# 同じ相対局所化の係数移送と全 nerve の同値

概要：Dwyer–Kan の既存の hammock 比較を、同じ自由局所化の実関手へ移す。
方針：元の二つの比較の係数自然性と二対三則を使う。
規約：元の Hom 射と実関手を保持し、モデル構造の仮定を追加しない。
使われ方：HA §4.2.3 の加群族で同じ底の局所化模型を比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
variable {C D : RelativeCategory.{u}} (F : C ⟶ D)

/-- 概要：同じ hammock Hom 射の弱同値性を自由局所化へ移す（Dwyer–Kan §9）。
方針：元の augmentation と比較の可換正方形に二対三則を使う。
規約：同じ localizationHomMap。使われ方：元の全 nerve 作用の充満忠実性。 -/
lemma localizationHomMap_weak_of_hammock (X Y : C.category)
    (h : IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
    IsWeakHomotopyEquivalence (localizationHomMap F X Y) := by
  have hm : IsWeakHomotopyEquivalence (freeHammockDiagonalMap F X Y) := by
    apply (freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence D
      (F.functor.obj X) (F.functor.obj Y)).cancel_right
    rw [freeHammockDiagonalMap_augmentation]
    exact (freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y).comp h
  apply (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y).cancel_left
  rw [← freeHammockDiagonalMap_comparison]
  exact hm.comp (freeHammockDiagonalComparison_isWeakHomotopyEquivalence D
    (F.functor.obj X) (F.functor.obj Y))

/-- 概要：同じ hammock Hom 比較から全 nerve の充満忠実性（HTT §1.1.5）。
方針：同じ Kan 化した Hom 射の弱同値性を nerve の判定に渡す。
規約：元の実関手。使われ方：加群族の局所化模型の比較。 -/
lemma localizationNerveMap_fullyFaithful_of_hammock
    (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
    IsFullyFaithful (localizationNerveMap F) := by
  apply (coherentNerveMap_isFullyFaithful_iff
    (C := KanLocalizationCategory C) (D := KanLocalizationCategory D)
    (kanLocalizationEnrichedMap F)).mpr
  intro X Y
  change IsQCatEquivalence
    (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
      (localizationHomMap F X Y))
  exact (isWeakHomotopyEquivalence_iff_isQCatEquivalence _).mp
    (Hammock.exInfinity_map_weak _ (localizationHomMap_weak_of_hammock F X Y (h X Y)))

variable (G : D ⟶ C)
/-- 概要：同じ弱余単位は実局所化関手の本質的全射性を与える（HTT §1.1.5）。
方針：元の逆候補の対象と同じ弱射の頂点同型を使う。
規約：元の対象表示。使われ方：全 nerve の同値判定。 -/
lemma localizationNerveMap_essentiallySurjective_of_counit
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsEssentiallySurjective (localizationNerveMap F) := by
  intro y
  obtain ⟨Y, rfl⟩ := (localizationNerveVertexEquiv D).surjective y
  refine ⟨localizationNerveVertexEquiv C (G.functor.obj Y), ⟨?_⟩⟩
  exact eqToIso (congrArg HomotopyCategory.mk (localizationNerveMap_vertex F (G.functor.obj Y))) ≪≫
    localizationNerveVertexIsoOfWeak D (ε.app Y) (hε Y)

/-- 概要：元の Hom 比較と同じ弱余単位から全 nerve の同値（HTT §1.1.5）。
方針：充満忠実性と本質的全射性を組み合わせる。
規約：元の実関手自身の同値性。使われ方：加群族の底の模型移送。 -/
lemma localizationNerveMap_isQCatEquivalence_of_hammock_counit
    (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y))
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsQCatEquivalence (localizationNerveMap F) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (localizationNerveMap_fullyFaithful_of_hammock F h)
    (localizationNerveMap_essentiallySurjective_of_counit F G ε hε)

/-- 概要：同じ両弱比較を持つ相対逆は元の全局所化関手の同値（Dwyer–Kan §9）。
方針：既存の hammock 判定を同じ自由局所化の全 nerve へ移す。
規約：元の二つの相対関手。使われ方：同じ代数・加群の模型の往復。 -/
lemma localizationNerveMap_isQCatEquivalence_of_weak_comparisons
    (η : F.functor ⋙ G.functor ⟶ 𝟭 C.category) (hη : ∀ X, C.weakEquivalences (η.app X))
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category) (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsQCatEquivalence (localizationNerveMap F) :=
  localizationNerveMap_isQCatEquivalence_of_hammock_counit F G
    (Hammock.RelativeEquivalence.colimitMap_weak F G η hη ε hε) ε hε

end SerrePositivity.EInfinity.Modules

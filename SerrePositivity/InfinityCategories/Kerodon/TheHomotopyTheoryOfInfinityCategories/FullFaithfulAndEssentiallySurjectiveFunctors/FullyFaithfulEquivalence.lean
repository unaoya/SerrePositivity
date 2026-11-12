module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathVertices

/-!
概要：充満忠実かつ本質的全射な関手の同値判定。
方針：可逆 path の置換を頂点全射な充満忠実 inner fibration にし、全境界を持ち上げる。
規約：同値は A3a の実際の逆射と関手単体集合での可逆二胞体。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX）、HTT §1.2.10 の同値判定。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：充満忠実性は可逆 path による置換へ移る。
方針：始域への射影は充満忠実で、置換された関手と射影後の元の関手は同型。
規約：両端の quasicategory 性を仮定する。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） の inner fibration への還元。 -/
lemma IsFullyFaithful.equivalencePathReplacementMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.isFullyFaithful_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementFunctorIso f)).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f)).comp hf)

/-- 概要：充満忠実かつ本質的全射なら quasicategory の同値。
方針：path の置換が trivial Kan fibration であることから逆射を構成する。
規約：写像空間の実際のホモトピー同値と頂点のホモトピー圏での同型を仮定する。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX）、HTT §1.2.10 の主判定。 -/
lemma isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_iff_equivalencePathReplacementMap f).mpr
    (hf.equivalencePathReplacementMap.isQCatEquivalence_of_surjective
      he.equivalencePathReplacementMap_surjective)

/-- 概要：充満忠実かつ本質的全射な関手から明示的な同値の逆データを選ぶ。
方針：主判定の逆射と二つの可逆二胞体を選択する。
規約：順方向の射は指定された f。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） の利用側 API。 -/
noncomputable def qCatEquivalenceOfFullyFaithfulEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y :=
  (isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective f hf he).choose

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

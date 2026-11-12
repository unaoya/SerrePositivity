module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：全部分複体への包含による関手 ∞ 圏の充満忠実性。
方針：内部 Hom の全部分複体表示と、包含の写像空間の厳密な同型を使う。
規約：パラメータの quasicategory 性は不要。
使われ方：B2 の余単位の可逆性を h Fun 全体で証明する際の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：全部分複体への包含による任意のパラメータの後合成は充満忠実。
方針：内部 Hom を頂点条件の全部分複体と同型に表示して包含を合成する。
規約：P の同型不変性やパラメータの quasicategory 性を仮定しない。
使われ方：反射の余単位と関手圏での局所化普遍性の入力。 -/
lemma isFullyFaithful_fullSubcomplexFunctorInclusion (A X : SSet.{u}) [Quasicategory X]
    (P : X _⦋0⦌ → Prop) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomForward_ι]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso A X P)).isQCatEquivalence.isFullyFaithful).comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

/-- 概要：包含による後合成は h Fun の通常の関手としても充満忠実。
方針：関手 ∞ 圏の充満忠実性から h への一般定理を使う。
規約：この定理は元の写像空間の充満忠実性の帰結。
使われ方：余単位の逆射の持ち上げと等式の反映。 -/
def fullSubcomplexFunctorInclusionHoFullyFaithful (A X : SSet.{u}) [Quasicategory X]
    (P : X _⦋0⦌ → Prop) :
    (hoFunctor.map ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)).toFunctor.FullyFaithful :=
  (isFullyFaithful_fullSubcomplexFunctorInclusion A X P).toHoFullyFaithful

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

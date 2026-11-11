module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ParameterizedFullFaithfulness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：全ての標的への前合成の h 圏での充満忠実性から写像空間の充満忠実性を得る。
方針：パラメータを内部 Hom の交換同型で標的へ移し、全パラメータ判定を適用する。
規約：始域の単体集合の quasicategory 性は不要。
使われ方：comma 射影への前合成の Hom 対応を実際の写像空間へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：全標的での h Fun の前合成の充満忠実性は写像空間での充満忠実性を導く。
方針：二つの内部 Hom の交換同型で、任意のパラメータを新しい標的へ組み込む。
規約：標的は元の単体集合と同じ宇宙の quasicategory。
使われ方：Hom 対応の族から元の関手圏の前合成の写像空間を比較する。 -/
lemma precomposition_isFullyFaithful_of_hoFullyFaithful {K C : SSet.{u}} (i : K ⟶ C)
    (h : ∀ (Z : SSet.{u}) [Quasicategory Z],
      (hoFunctor.map ((pre i).app Z)).toFunctor.FullyFaithful)
    (D : SSet.{u}) [Quasicategory D] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre i).app D) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_of_parameterized_hoFullyFaithful
  intro A _
  let e₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A C D)).isFullyFaithful.toHoFullyFaithful
  let e₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A K D)).isFullyFaithful.toHoFullyFaithful
  have he :
      (hoFunctor.map ((ihom A).map ((pre i).app D))).toFunctor ⋙
        (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A K D).hom).toFunctor =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A C D).hom).toFunctor ⋙
        (hoFunctor.map ((pre i).app ((ihom A).obj D))).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre, CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor]
  have ht : ((hoFunctor.map ((ihom A).map ((pre i).app D))).toFunctor ⋙
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A K D).hom).toFunctor).FullyFaithful := by
    rw [he]
    exact e₀.comp (h ((ihom A).obj D))
  have : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A K D).hom).toFunctor.Faithful := e₁.faithful
  exact CategoryTheory.Functor.FullyFaithful.ofCompFaithful ht

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

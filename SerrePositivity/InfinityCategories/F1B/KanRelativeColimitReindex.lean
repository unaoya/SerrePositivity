module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeInitialComparison
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：単射な前合成同値に沿う標準 U 余極限の添字変更。
方針：二つの coslice の制限は自明 Kan fibration であり、後合成と可換である。
規約：余錐の頂点と U による像を同じ射で制限する。
使われ方：comma fiber の局所条件を元の Kan 添字へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：単射な前合成同値で制限した余錐は元の余錐と同じ相対余極限性を持つ。
方針：coslice の制限の充満忠実性と頂点全射性を相対始対象の比較へ渡す。
規約：U の充填性と添字の quasicategory 性を要求しない。
使われ方：標準局所 Kan 図式と comma fiber の相対普遍性の比較。 -/
lemma kanIsRelativeColimitCone_iff_restrict_of_precompositionEquivalence
    {A K D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) {p : K ⟶ D} (c : JoinCocone p) (i : A ⟶ K) [Mono i]
    (hi : IsPrecompositionEquivalence i) :
    IsRelativeColimitCone U c ↔ IsRelativeColimitCone U (c.restrict i) := by
  have := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence p i hi
  have := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence (p ≫ U) i hi
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (sliceUnderRestrict p i)
  have hsurj : Function.Surjective ((sliceUnderRestrict p i).app (Opposite.op ⦋0⦌)) := by
    intro y
    exact ⟨s.app (Opposite.op ⦋0⦌) y,
      ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) y⟩
  exact kanRelativeInitialVertex_iff_of_comparison
    (sliceUnderPostcomp p U) (sliceUnderPostcomp (i ≫ p) U)
    (sliceUnderRestrict p i) (sliceUnderRestrict (p ≫ U) i)
    (sliceUnderRestrict_postcomp p i U).symm
    (isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful
    (isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful hsurj c

end SerrePositivity.InfinityCategories.F1B

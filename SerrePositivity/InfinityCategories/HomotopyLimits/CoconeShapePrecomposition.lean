module

public import SerrePositivity.InfinityCategories.Stable.CosliceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.Simplicial.InnerAnodyneReplacement
public import SerrePositivity.InfinityCategories.F2.CoconeValEquality
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction

/-!
概要：単射な前合成同値に沿い、元の全余錐を延長して同じ余極限性を保存・反映する。
方針：余錐圏の制限の自明 Kan 性と、全 join 写像への厳密な関手延長を使う。
規約：添字の quasicategory 性は要求せず、元の全余錐の制限を等式で保持する。
使われ方：任意の小さい添字を quasicategory へ置換して保存性を判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
/-- 同じ全余錐の制限は、添字の充填性を仮定せず余極限性を保存・反映する。 -/
lemma isColimitCone_iff_restrict_mono_precomposition
    {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (hi : IsPrecompositionEquivalence i)
    {p : B ⟶ X} (c : JoinCocone p) :
    IsColimitCone c ↔ IsColimitCone (c.restrict i) := by
  have : TrivialKanFibration (sliceUnderRestrict p i) :=
    sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence p i hi
  exact (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict p i)).isInitialVertex_iff c
/-- 元の全余錐は、同じ単射な前合成同値に沿って厳密に延長できる。 -/
lemma exists_coconeExtension_of_mono_precomposition
    {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (hi : IsPrecompositionEquivalence i)
    {p : A ⟶ X} (c : JoinCocone p) :
    ∃ (q : B ⟶ X) (d : JoinCocone q), (d.restrict i).val = c.val := by
  let j := joinMap i (𝟙 (Δ[0] : SSet.{u}))
  have hj := hi.joinMap_left (Δ[0] : SSet.{u})
  obtain ⟨v, hv⟩ := pre_surjective_of_essentiallySurjective j
    (hj X).choose.isEssentiallySurjective (functorVertex c.val)
  let L := (functorVertexEquiv _ X).symm v
  have hL : j ≫ L = c.val := by
    apply functorVertex_injective
    change ((pre j).app X).app (Opposite.op ⦋0⦌) (functorVertexEquiv _ X L) = _
    rw [Equiv.apply_symm_apply]
    exact hv
  exact ⟨joinInl B Δ[0] ≫ L, ⟨L, rfl⟩, hL⟩
end SerrePositivity.InfinityCategories.HomotopyLimits

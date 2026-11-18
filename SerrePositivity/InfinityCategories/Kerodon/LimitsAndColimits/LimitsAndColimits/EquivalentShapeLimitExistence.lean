module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.EquivalentRestrictionColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitDiagramIso

/-!
概要：同値な添字への制限から、元の指定図式の極限の存在を回収する。
方針：既存の単射・trivial Kan 因子分解と、その単射の同値による制限判定を使う。
使われ方：HTT 4.1.3.1、Kerodon §7.1（Tag 02K2）の添字変更、重み付き切断。
規約：元の添字写像に単射性を追加しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同値な形状への制限が極限を持てば元の同じ図式も極限を持つ。 -/
lemma hasLimit_of_equivalentRestriction {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (hf : IsQCatEquivalence f) (F : B ⟶ X)
    (hF : HasLimit (f ≫ F)) : HasLimit F := by
  obtain ⟨Z, i, p, hi, hp, he⟩ := exists_mono_trivialKan_factorization f
  have : Mono i := hi
  have : TrivialKanFibration p := hp
  have : Quasicategory Z := quasicategory_of_innerFibration p
  have hp' := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence
  have hi' : IsQCatEquivalence i := hp'.cancel_right (he.symm ▸ hf)
  have hsmall : HasLimit (i ≫ (p ≫ F)) := by
    simpa only [← Category.assoc, he] using hF
  have hlarge : HasLimit (p ≫ F) :=
    (hasLimit_iff_restrict_of_precompositionEquivalence (p ≫ F) i
      hi'.isPrecompositionEquivalence).mpr hsmall
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section p
  have : Mono s := mono_of_mono_fac hs
  have hsp : IsQCatEquivalence (s ≫ p) := by
    rw [hs]
    exact (QCatEquivalence.refl B).isQCatEquivalence
  have hs' : IsQCatEquivalence s := hp'.cancel_right hsp
  have hrestrict := (hasLimit_iff_restrict_of_precompositionEquivalence (p ≫ F) s
    hs'.isPrecompositionEquivalence).mp hlarge
  simpa only [← Category.assoc, hs, Category.id_comp] using hrestrict

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

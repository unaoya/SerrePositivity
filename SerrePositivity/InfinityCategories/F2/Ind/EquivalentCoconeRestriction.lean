module

public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F1.BoundaryFactorization

/-!
概要：任意の比較同値による元の全余錐圏の制限は同値で、指定余錐の余極限性を保存・反映する。
方針：単射と自明 Kan fibration の分解を同じ全余錐圏の制限へ写す。
規約：元の比較に単射性を仮定しない。
使われ方：小さい元の圏上の同じ密度余錐から標準 Kan 余錐の余極限性へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 任意の比較同値による、元の全余錐圏の制限自体が同値。 -/
lemma sliceUnderRestrict_equivalence_of_equivalentShape {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (hf : IsQCatEquivalence f) (F : B ⟶ X) :
    IsQCatEquivalence (sliceUnderRestrict F f) := by
  obtain ⟨Z, i, p, hi, hp, he⟩ := exists_mono_trivialKan_factorization f
  have : Mono i := hi
  have : TrivialKanFibration p := hp
  have : Quasicategory Z := quasicategory_of_innerFibration p
  have hp' := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence
  have hi' : IsQCatEquivalence i := hp'.cancel_right (he.symm ▸ hf)
  have : TrivialKanFibration (sliceUnderRestrict (p ≫ F) i) :=
    sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence
      (p ≫ F) i hi'.isPrecompositionEquivalence
  have hc := (sliceUnderRestrict_equivalence_of_trivialKan p F).comp
    (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict (p ≫ F) i)).isQCatEquivalence
  change IsQCatEquivalence (sliceUnderRestrict F p ≫ sliceUnderRestrict (p ≫ F) i) at hc
  rw [sliceUnderRestrict_comp] at hc
  exact (congrArg (fun g : A ⟶ B => IsQCatEquivalence (sliceUnderRestrict F g)) he).mp hc

/-- 元の比較同値への制限は、指定した同じ余錐の余極限性を保存・反映する。 -/
lemma isColimitCone_iff_restrict_equivalentShape {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (hf : IsQCatEquivalence f) {F : B ⟶ X} (c : JoinCocone F) :
    IsColimitCone c ↔ IsColimitCone (c.restrict f) :=
  (sliceUnderRestrict_equivalence_of_equivalentShape f hf F).choose.isInitialVertex_iff c

end SerrePositivity.InfinityCategories.F2.Ind

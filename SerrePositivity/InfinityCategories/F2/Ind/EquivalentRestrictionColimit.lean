module

public import SerrePositivity.InfinityCategories.F1.Simplicial.BoundaryFactorization
public import SerrePositivity.InfinityCategories.Stable.ColimitDiagramIso

/-!
概要：任意の同値な形状への制限が余極限を持てば、元の図式も余極限を持つ。
方針：単射と自明 Kan fibration に分解し、両方の同値な単射で存在を移す。
規約：元の比較射に単射性を要求しない。
使われ方：小さい元の圏の余極限から Indκ の局所 Kan 図式の余極限を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同値な元の形状への制限から、元の図式自身の余極限の存在を回収する。 -/
lemma hasColimit_of_equivalentRestriction {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (hf : IsQCatEquivalence f) (F : B ⟶ X)
    (hF : HasColimit (f ≫ F)) : HasColimit F := by
  obtain ⟨Z, i, p, hi, hp, he⟩ := exists_mono_trivialKan_factorization f
  have : Mono i := hi
  have : TrivialKanFibration p := hp
  have : Quasicategory Z := quasicategory_of_innerFibration p
  have hp' := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence
  have hi' : IsQCatEquivalence i := hp'.cancel_right (he.symm ▸ hf)
  have hsmall : HasColimit (i ≫ (p ≫ F)) := by
    simpa only [← Category.assoc, he] using hF
  have hlarge : HasColimit (p ≫ F) :=
    (hasColimit_iff_restrict_of_precompositionEquivalence (p ≫ F) i
      hi'.isPrecompositionEquivalence).mpr hsmall
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section p
  have : Mono s := mono_of_mono_fac hs
  have hsp : IsQCatEquivalence (s ≫ p) := by
    rw [hs]
    exact (QCatEquivalence.refl B).isQCatEquivalence
  have hs' : IsQCatEquivalence s := hp'.cancel_right hsp
  have hrestrict := (hasColimit_iff_restrict_of_precompositionEquivalence (p ≫ F) s
    hs'.isPrecompositionEquivalence).mp hlarge
  simpa only [← Category.assoc, hs, Category.id_comp] using hrestrict

end SerrePositivity.InfinityCategories.F2.Ind

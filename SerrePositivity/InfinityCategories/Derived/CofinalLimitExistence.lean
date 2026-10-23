module
public import SerrePositivity.InfinityCategories.F1B.CofinalFactorizationCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
/-!
概要：left cofinal な任意の実写像による制限から、元の図式の極限の存在を回収する。
方針：left anodyne・trivial Kan 因子分解で錐を延長し、後因子の同値な単射切断へ制限する。
規約：cofinal 写像自体の単射性を要求しない。使われ方：実分母図式から右 Kan 局所極限への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- left cofinal な任意の写像への制限が極限を持てば、元の図式も極限を持つ。 -/
lemma hasLimit_of_leftCofinal {A B X : SSet.{u}} [Quasicategory B] [Quasicategory X]
    (u : A ⟶ B) (hu : IsLeftCofinal u) (F : B ⟶ X) (h : HasLimit (u ≫ F)) : HasLimit F := by
  obtain ⟨Z, j, p, hm, hj, hp, he⟩ := hu.exists_anodyne_trivialKan_factorization
  have : Mono j := hm
  have : TrivialKanFibration p := hp
  have : Quasicategory Z := quasicategory_of_innerFibration p
  have h' : HasLimit (j ≫ (p ≫ F)) := by
    simpa only [← Category.assoc, he] using h
  obtain ⟨d, hd⟩ := h'
  have : TrivialKanFibration (sliceOverRestrict (p ≫ F) j) :=
    sliceOverRestrict_trivialKanFibration (p ≫ F) j hj
  obtain ⟨c, hc, _, _⟩ := F2.exists_limitCone_extension_of_trivialRestriction (p ≫ F) j d hd
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section p
  have : Mono s := by
    have : Mono (s ≫ p) := by rw [hs]; infer_instance
    exact mono_of_mono_fac hs
  have hp' := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence
  have hsp : IsQCatEquivalence (s ≫ p) := by
    rw [hs]
    exact (qCatEquivalenceOfIso (Iso.refl B)).isQCatEquivalence
  have hs' := hp'.cancel_right hsp
  have : TrivialKanFibration (sliceOverRestrict (p ≫ F) s) :=
    F2.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence
      (p ≫ F) s hs'.isPrecompositionEquivalence
  have ht : IsLimitCone (F2.restrictJoinCone c s) :=
    (qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict (p ≫ F) s)).map_isTerminalVertex hc
  have hr : HasLimit (s ≫ (p ≫ F)) := ⟨F2.restrictJoinCone c s, ht⟩
  simpa only [← Category.assoc, hs, Category.id_comp] using hr
end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationRestriction
public import SerrePositivity.InfinityCategories.F1B.KanLeftCanonicalMapping
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison

/-!
概要：標準左 Kan 条件を満たす図式の全余錐の制限は同値。
方針：定値標的への元の写像空間の同値を native 余錐空間へ戻し、全 fiber の判定を使う。
規約：元の添字写像の単射性も、標的図式の普遍性も仮定しない。
使われ方：各段の密度表示と全空間の余極限を比較する Kan の合成入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A K X : SSet.{u}} [Quasicategory A] [Quasicategory K] [Quasicategory X]
  (i : A ⟶ K) (F : K ⟶ X)
  (hF : ∀ k, IsColimitCone (leftKanCanonicalCocone i F k))
include hF

/-- 標準左 Kan 図式から定値標的への同じ全変換の制限は同値。 -/
lemma constantTransformationRestriction_isQCatEquivalence (z : X _⦋0⦌) :
    IsQCatEquivalence (constantTransformationRestriction i F z) := by
  have h := (F1B.kanLeftCanonical_pinchedHomMap_equivalence i F hF (SSet.const z)).isQCatEquivalence
  have h₀ := functorVertex_precomposition i F
  have h₁ : ((pre i).app X).app (Opposite.op ⦋0⦌) (functorVertex (SSet.const z)) =
      functorVertex (SSet.const z) := by
    rw [functorVertex_precomposition, SSet.comp_const]
  have he : IsQCatEquivalence
      (eqToHom (congrArg₂ (fun a b => pinchedHom a b) h₀ h₁)) :=
    (qCatEquivalenceOfIso (eqToIso
      (congrArg₂ (fun a b => pinchedHom a b) h₀ h₁))).isQCatEquivalence
  have ht := (h.comp he).comp (pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (functorVertex (i ≫ F)) (functorVertex (SSet.const z)))
  have hc := pinchedHomToIntervalMappingSpace_postOfEq ((pre i).app X)
    (functorVertex F) (functorVertex (SSet.const z)) h₀ h₁
  rw [hc] at ht
  exact (pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (functorVertex F) (functorVertex (SSet.const z))).cancel_left ht

/-- 標準左 Kan 図式の、指定終点を持つ元の native 余錐空間の制限は同値。 -/
lemma kanCanonical_cosliceRestrictionFiberMap_isQCatEquivalence (z : X _⦋0⦌) :
    IsQCatEquivalence (cosliceRestrictionFiberMap F i z) := by
  have h := (F2.coconeTransformationMap_isQCatEquivalence F z).comp
    (constantTransformationRestriction_isQCatEquivalence i F hF z)
  rw [← coconeTransformationMap_restrict] at h
  exact (F2.coconeTransformationMap_isQCatEquivalence (i ≫ F) z).cancel_right h

/-- 標準左 Kan 図式の全余錐圏への実際の制限射自体が同値。 -/
lemma kanCanonical_sliceUnderRestrict_isQCatEquivalence :
    IsQCatEquivalence (sliceUnderRestrict F i) := by
  apply isQCatEquivalence_of_leftFibration_fibers
    (sliceUnderProjection F) (sliceUnderProjection (i ≫ F))
    (sliceUnderRestrict F i) (sliceUnderRestrict_projection F i)
  exact kanCanonical_cosliceRestrictionFiberMap_isQCatEquivalence i F hF

/-- 標準左 Kan 図式の指定全余錐は、同じ添字制限が余極限であるとき、かつそのときに限り余極限。 -/
lemma kanCanonical_isColimitCone_iff_restrict (c : JoinCocone F) :
    IsColimitCone c ↔ IsColimitCone (c.restrict i) :=
  (kanCanonical_sliceUnderRestrict_isQCatEquivalence i F hF).choose.isInitialVertex_iff c

end SerrePositivity.InfinityCategories.F2.Ind

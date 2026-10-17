module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonRestriction
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthModule
public import SerrePositivity.DifferentialGraded.Derived.RestrictionShift
public import SerrePositivity.DifferentialGraded.Verdier.Tria
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-! # 商の導来制限の像は指定有限 cell に対して局所的

代表加群上の零性から全ての指定有限 cell 上の右直交性へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商の任意の導来加群の制限は、S で生成される全有限 cell に右直交する。 -/
lemma quotientDerivedRestriction_rightOrthogonal (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) :
    (derivedFiniteCellOver A D S).rightOrthogonal
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X) := by
  let R := dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)
  let : R.CommShift ℤ := dgDerivedRestrictionCommShift A D _ _
  let : R.essImage.IsStableUnderShift ℤ := {
    isStableUnderShiftBy := fun n => {
      le_shift := by
        rintro Y ⟨Z, ⟨e⟩⟩
        exact ⟨Z⟦n⟧, ⟨(R.commShiftIso n).app Z ≪≫ (shiftFunctor _ n).mapIso e⟩⟩ } }
  have hle : derivedFiniteCellOver A D S ≤ R.essImage.leftOrthogonal :=
    (derivedFiniteCellOver_le_iff_generators A D R.essImage.leftOrthogonal S).2 (by
      intro b hb Y f hY
      obtain ⟨Z, ⟨e⟩⟩ := hY
      apply (cancel_mono e.inv).1
      rw [zero_comp]
      exact (quotientDerivedRestriction_representable_hom_subsingleton A D S Z ⟨b, hb⟩).elim _ _)
  intro Y f hY
  exact hle Y hY f ⟨X, ⟨Iso.refl _⟩⟩

/-- 制限の像への Hom は、指定有限 cell の cone を持つ射の前置で変わらない。 -/
lemma quotientDerivedRestriction_isLocal (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) :
    (derivedFiniteCellOver A D S).trW.isLocal
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X) := by
  rw [ObjectProperty.isLocal_trW]
  exact quotientDerivedRestriction_rightOrthogonal A D S X

/-- tria(D) に制限した Hom も、U17a の指定 Verdier 分母の前置で不変。 -/
lemma quotientDerivedRestriction_tria_precomp_bijective (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S))
    {M N : TriaCategory A D} (s : M ⟶ N) (hs : (triaImage A D S).trW s) :
    Function.Bijective (fun f : (triaInclusion A D).obj N ⟶
      (dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X =>
        (triaInclusion A D).map s ≫ f) :=
  quotientDerivedRestriction_isLocal A D S X _
    (((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s).1 hs)

/-- 実際の制限代表加群の導来像も、置換なしで局所対象になる。 -/
lemma quotientRepresentableRestriction_isLocal (S : Set D) (z : D) :
    (derivedFiniteCellOver A D S).trW.isLocal ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) := by
  let M : ModuleCategory A (QuotientObject D S) :=
    ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S))
  have h := quotientDerivedRestriction_isLocal A D S
    ((moduleToDerived A (QuotientObject D S)).obj M)
  have he := congrArg (fun F => F.obj M)
    (dgDerivedRestriction_fac A D (QuotientObject D S) (inclusion A D S))
  change (dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj
      ((moduleToDerived A (QuotientObject D S)).obj M) = _ at he
  rw [he] at h
  exact h

lemma quotientRepresentableRestriction_tria_precomp_bijective (S : Set D) (z : D)
    {M N : TriaCategory A D} (s : M ⟶ N) (hs : (triaImage A D S).trW s) :
    Function.Bijective (fun f : (triaInclusion A D).obj N ⟶
      (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z)) =>
          (triaInclusion A D).map s ≫ f) :=
  quotientRepresentableRestriction_isLocal A D S z _
    (((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s).1 hs)

end SerrePositivity.DifferentialGraded.DGQuotient

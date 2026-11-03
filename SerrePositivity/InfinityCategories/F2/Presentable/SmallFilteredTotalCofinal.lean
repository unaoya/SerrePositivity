module
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredRetracts

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFilteredTotal
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.RightKanShapeIso
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.F1B.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredEquivalence
public import SerrePositivity.InfinityCategories.Stable.Filtered.FilteredWeakContractibility
public import SerrePositivity.InfinityCategories.Core.InnerPullback

/-!
概要：部分添字の全空間から元の添字への値射影は right cofinal。
方針：通常の comma を上方部分 poset と比較し、filtered 性を native な coslice へ移す。
規約：同じ値射影について Quillen A を適用する。cofinal 性を instance で仮定しない。
使われ方：小さい部分余極限を組み立て、元の全余極限を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]

/-- 元の上方部分 poset を、値射影の同じ通常の comma として読む関手。 -/
def smallFilteredAboveToComma (i : I) : SmallFilteredTotalAbove κ μ i ⥤
    StructuredArrow i (smallFilteredTotalValue (κ := κ) (μ := μ)) where
  obj x := StructuredArrow.mk (homOfLE x.property)
  map f := StructuredArrow.homMk (homOfLE (leOfHom f)) (by subsingleton)

/-- 同じ comma の元の値を、上方部分 poset へ戻す関手。 -/
def smallFilteredCommaToAbove (i : I) :
    StructuredArrow i (smallFilteredTotalValue (κ := κ) (μ := μ)) ⥤
      SmallFilteredTotalAbove κ μ i where
  obj x := ⟨x.right, leOfHom x.hom⟩
  map f := homOfLE (leOfHom f.right)

/-- 同じ上方部分 poset と元の値射影の comma の明示的な同値。 -/
def smallFilteredAboveCommaEquivalence (i : I) : SmallFilteredTotalAbove κ μ i ≌
    StructuredArrow i (smallFilteredTotalValue (κ := κ) (μ := μ)) where
  functor := smallFilteredAboveToComma i
  inverse := smallFilteredCommaToAbove i
  unitIso := NatIso.ofComponents (fun x ↦ eqToIso (Subtype.ext rfl))
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _)
    (by subsingleton)) (fun _ ↦ by apply StructuredArrow.hom_ext; subsingleton)

variable [Fact μ.IsRegular] [IsCardinalFiltered I κ] (h : IsCardinalChangeBound κ μ)
include h

/-- 元の値射影の各 native な coslice 引き戻しは filtered なので弱可縮。 -/
lemma smallFilteredTotalValue_coslice_isWeaklyContractible (i : I) :
    IsWeaklyContractible (pullback (nerveMap (smallFilteredTotalValue (κ := κ) (μ := μ)))
      (sliceUnderProjection (nervePoint i))) := by
  have := smallFilteredTotalAbove_isCardinalFiltered h i
  have : IsKappaFiltered κ (nerve (SmallFilteredTotalAbove κ μ i)) :=
    Ind.isKappaFiltered_nerve_of_cardinalFiltered _
  have : IsKappaFiltered κ
      (nerve (StructuredArrow i (smallFilteredTotalValue (κ := κ) (μ := μ)))) :=
    (isKappaFiltered_iff_of_equivalence
      (SerrePositivity.InfinityCategories.F1B.nerveQCatEquivalence (smallFilteredAboveCommaEquivalence i))).mp inferInstance
  have := isFilteredInfinity_of_isKappaFiltered
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular))
    (nerve (StructuredArrow i (smallFilteredTotalValue (κ := κ) (μ := μ))))
  let e := SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso i
    (smallFilteredTotalValue (κ := κ) (μ := μ)) ≪≫ pullbackSymmetry _ _
  have : IsFilteredInfinity
      (pullback (nerveMap (smallFilteredTotalValue (κ := κ) (μ := μ)))
        (sliceUnderProjection (nervePoint i))) :=
    (isFilteredInfinity_iff_of_iso e).mp inferInstance
  exact isWeaklyContractible_of_isFilteredInfinity _

/-- 元の部分添字の全空間から元の添字への同じ値射影は right cofinal。 -/
lemma smallFilteredTotalValue_isRightCofinal :
    IsRightCofinal (nerveMap (smallFilteredTotalValue (κ := κ) (μ := μ) (I := I))) := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro v
  have hv : v = nerveVertex (nerveEquiv v) := (nerveEquiv.left_inv v).symm
  rw [hv]
  exact smallFilteredTotalValue_coslice_isWeaklyContractible h _

/-- 宇宙 u+1 の元の全余錐は、同じ全空間への制限で余極限性を保ち反映する。 -/
lemma smallFilteredTotal_restrict_isColimit_iff {C : SSet.{u + 1}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C} (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (c.restrict
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (smallFilteredTotalValue (κ := κ) (μ := μ))))) :=
  Ind.isColimitCone_iff_restrict_rightCofinal _
    (Ind.isRightCofinal_ulift _ (smallFilteredTotalValue_isRightCofinal h)) c

end SerrePositivity.InfinityCategories.F2.Presentable

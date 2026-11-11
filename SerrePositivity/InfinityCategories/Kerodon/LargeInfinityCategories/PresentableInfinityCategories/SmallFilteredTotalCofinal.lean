module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredRetracts

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotal
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightKanShapeIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback

/-!
概要：部分添字の全空間から元の添字への値射影は right cofinal。
方針：通常の comma を上方部分 poset と比較し、filtered 性を native な coslice へ移す。
規約：同じ値射影について Quillen A を適用する。cofinal 性を instance で仮定しない。
使われ方：小さい部分余極限を組み立て、元の全余極限を回収する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]

/-- 元の上方部分 poset を、値射影の同じ通常の comma として読む関手。 -/
def smallFilteredAboveToComma (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotalAbove κ μ i ⥤
    StructuredArrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ)) where
  obj x := StructuredArrow.mk (homOfLE x.property)
  map f := StructuredArrow.homMk (homOfLE (leOfHom f)) (by subsingleton)

/-- 同じ comma の元の値を、上方部分 poset へ戻す関手。 -/
def smallFilteredCommaToAbove (i : I) :
    StructuredArrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ)) ⥤
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotalAbove κ μ i where
  obj x := ⟨x.right, leOfHom x.hom⟩
  map f := homOfLE (leOfHom f.right)

/-- 同じ上方部分 poset と元の値射影の comma の明示的な同値。 -/
def smallFilteredAboveCommaEquivalence (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotalAbove κ μ i ≌
    StructuredArrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ)) where
  functor := smallFilteredAboveToComma i
  inverse := smallFilteredCommaToAbove i
  unitIso := NatIso.ofComponents (fun x ↦ eqToIso (Subtype.ext rfl))
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _)
    (by subsingleton)) (fun _ ↦ by apply StructuredArrow.hom_ext; subsingleton)

variable [Fact μ.IsRegular] [IsCardinalFiltered I κ] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
include h

/-- 元の値射影の各 native な coslice 引き戻しは filtered なので弱可縮。 -/
lemma smallFilteredTotalValue_coslice_isWeaklyContractible (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint i))) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalAbove_isCardinalFiltered h i
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotalAbove κ μ i)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ
      (nerve (StructuredArrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ)))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_equivalence
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveQCatEquivalence (smallFilteredAboveCommaEquivalence i))).mp inferInstance
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular))
    (nerve (StructuredArrow i (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ))))
  let e := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ)) ≪≫ pullbackSymmetry _ _
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity
      (pullback (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint i))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_iff_of_iso e).mp inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity _

/-- 元の部分添字の全空間から元の添字への同じ値射影は right cofinal。 -/
lemma smallFilteredTotalValue_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ) (I := I))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro v
  have hv : v = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (nerveEquiv v) := (nerveEquiv.left_inv v).symm
  rw [hv]
  exact smallFilteredTotalValue_coslice_isWeaklyContractible h _

/-- 宇宙 u+1 の元の全余錐は、同じ全空間への制限で余極限性を保ち反映する。 -/
lemma smallFilteredTotal_restrict_isColimit_iff {C : SSet.{u + 1}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue (κ := κ) (μ := μ))))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (smallFilteredTotalValue_isRightCofinal h)) c

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

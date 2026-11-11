module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedSimplexCategory
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility

/-!
概要：上方共終な directed poset 写像の nerve は native に right cofinal。
方針：各 comma を上方部分 poset と比較し、その filtered 性から弱可縮性を得る。
規約：通常の Final 性だけを結論にしない。使われ方：共通小部分表示族の射影。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 上方部分 poset は、単調写像の元の右 comma と同値。 -/
def monotoneUpperCommaEquivalence {P Q : Type u} [Preorder P] [Preorder Q]
    {f : P → Q} (hf : Monotone f) (q : Q) :
    {p : P // q ≤ f p} ≌ StructuredArrow q hf.functor where
  functor := {
    obj := fun p ↦ StructuredArrow.mk (homOfLE p.property)
    map := fun g ↦ StructuredArrow.homMk (homOfLE (leOfHom g)) (by subsingleton) }
  inverse := {
    obj := fun a ↦ ⟨a.right, leOfHom a.hom⟩
    map := fun g ↦ homOfLE (leOfHom g.right) }
  unitIso := NatIso.ofComponents (fun p ↦ eqToIso (Subtype.ext rfl))
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _)
    (by subsingleton)) (fun _ ↦ by apply StructuredArrow.hom_ext; subsingleton)

/-- 上方共終な directed poset 写像は、元の全 nerve で right cofinal。 -/
lemma monotone_nerveMap_isRightCofinal {P Q : Type u} [Preorder P] [Preorder Q]
    [IsDirectedOrder P] {f : P → Q} (hf : Monotone f)
    (h : ∀ q, ∃ p, q ≤ f p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap hf.functor) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nerveMap_isRightCofinal_of_weaklyContractible_comma
  intro q
  let U := {p : P // q ≤ f p}
  have : Nonempty U := by
    obtain ⟨p, hp⟩ := h q
    exact ⟨⟨p, hp⟩⟩
  have : IsDirectedOrder U := by
    constructor
    intro a b
    obtain ⟨p, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨p, a.property.trans (hf ha)⟩, ha, hb⟩
  have : IsFiltered U := inferInstance
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : IsCardinalFiltered U Cardinal.aleph0 := (isCardinalFiltered_aleph0_iff U).mpr inferInstance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered Cardinal.aleph0 (nerve U) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered U
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered Cardinal.aleph0 (nerve (StructuredArrow q hf.functor)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_equivalence
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveQCatEquivalence (monotoneUpperCommaEquivalence hf q))).mp inferInstance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (nerve (StructuredArrow q hf.functor)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered le_rfl _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

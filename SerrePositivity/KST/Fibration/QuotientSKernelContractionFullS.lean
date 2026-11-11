module
public import SerrePositivity.KST.Fibration.QuotientSKernelContractionImage
public import SerrePositivity.KST.Fibration.ZeroEndPostcompSAction

/-! # 元の商核円柱の像を、同じ零値完全関手族の全 S_n 作用と厳密に照合する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 指定 Verdier 列の同じ実包含・商の合成は、全関手圏で零値頂点を表す。 -/
theorem verdierSequenceComposite_zero (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i.hom ≫ q.hom)) :=
  isZeroVertex_functorVertex_of_pointwise _ h.kills_inclusion

/-- 元の商核四角形の上辺は、包含後に元の S_n の実合成を厳密に回収する。 -/
theorem quotientSKernelTop_fullS (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    (relativeSFunctorMap i q.hom n ≫ relativeSQuotientMap q n) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj)).ι =
      (relativeSKernelTopIso h n).hom ≫
        (sExactMap n (show A ⟶ C from (show A ⟶ B from i) ≫
          (show B ⟶ C from q))).hom := by
  rw [Category.assoc, relativeSQuotientMap_ι, ← Category.assoc,
    relativeSFunctorMap_ι, Category.assoc, relativeSKernelTopIso_hom_inclusion]
  exact congrArg ((relativeSConstruction (i.hom ≫ q.hom) n).ι ≫ ·)
    (sPostcomp_comp n i.hom q.hom (exactMap_preservesSData i)
      (exactMap_preservesSData q)).symm

/-- 同じ商核円柱の全時刻像は、元の零値完全関手族の同じ全 S_n 作用である。 -/
theorem quotientSKernelContractionImage_fullS (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (n : SimplexCategoryᵒᵖ) :
    (quotientSKernelContractionImage h).app n ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι =
      ((relativeSKernelTopIso h n.unop.len).hom ▷ (Δ[1] : SSet.{u})) ≫
        zeroEndPostcompSAction
          (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h) n.unop.len := by
  change (((relativeSKernelTopIso h n.unop.len).hom ▷ (Δ[1] : SSet.{u})) ≫
    stableZeroSContractionAction A n.unop.len ≫ (relativeSKernelTopIso h n.unop.len).inv) ≫
      ((relativeSFunctorMap i q.hom n.unop.len ≫ relativeSQuotientMap q n.unop.len) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι) = _
  rw [quotientSKernelTop_fullS h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [zeroEndPostcompSAction_eq]

end SerrePositivity.KST.Fibration

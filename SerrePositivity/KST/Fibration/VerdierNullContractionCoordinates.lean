module
public import SerrePositivity.KST.Fibration.VerdierNullContractionComparison
public import SerrePositivity.KST.Fibration.QuotientSKernelContractionFullS

/-! # 指定 Verdier 二胞体と元の包含・商の、同じ全収縮族の対象座標の照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private theorem zeroEndPostcompFamily_eq_heq {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C) (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom))
    (hG : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G.hom)) (h : F = G) :
    HEq (zeroEndPostcompFamily F hF) (zeroEndPostcompFamily G hG) := by
  cases h
  rfl

private theorem zeroEndPostcompFamily_transport_heq {A C A' C' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hC : C = C') (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom))
    (hF' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (exactMapTransport hA hC F).hom)) :
    HEq (zeroEndPostcompFamily (exactMapTransport hA hC F) hF')
      (zeroEndPostcompFamily F hF) := by
  cases hA
  cases hC
  rfl

/-- 元の指定包含・商の同じ全収縮族と、二胞体の元の対象座標の族は異種等号で一致。 -/
theorem verdierNullContractionFamily_original_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence d.inclusion d.projection) :
    HEq (zeroEndPostcompFamily (A := d.left) (C := d.right)
      (show d.left ⟶ d.right from (show d.left ⟶ d.middle from d.inclusion) ≫
        (show d.middle ⟶ d.right from d.projection)) (verdierSequenceComposite_zero h))
      (verdierNullContractionFamily d) := by
  let F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right :=
    show d.left ⟶ d.right from (show d.left ⟶ d.middle from d.inclusion) ≫
      (show d.middle ⟶ d.right from d.projection)
  let G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap d.left d.right := verdierNullCompositeOriginalMap d 1
  have hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom) := verdierSequenceComposite_zero h
  have hG : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G.hom) :=
    isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeOriginalMap_zero d 1)
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierNullCompositeMap d 1).hom) :=
    isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeMap_zero d 1)
  have he : F = G := (verdierNullCompositeOriginalMap_lower d).symm
  have h₁ := zeroEndPostcompFamily_eq_heq (A := d.left) (C := d.right) F G hF hG he
  have h₂ := zeroEndPostcompFamily_transport_heq (verdierNullDiagonal_source d)
    (verdierNullDiagonal_target d) (verdierNullCompositeMap d 1) hz hG
  exact h₁.trans h₂

end SerrePositivity.KST.Fibration

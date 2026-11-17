module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedNerveOppositeSimplex

/-! 元の同じ全pairingの両端交換と反対表示の照合。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 元の同じpairingの全単体の写像は、反対表示と両端交換で厳密に元へ戻る。 -/
lemma twistedPairingNerveMap_opposite_swap {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) :
    twistedPairingNerveMap (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op)
      (by
        intro i j f
        apply Quiver.Hom.unop_inj
        simp only [CategoryTheory.unop_comp, Quiver.Hom.unop_op, Category.assoc]
        change (A.map f).unop ≫ h i ≫ B.map f = h j
        exact hh f) ≫
      edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
        twistedArrowOppositeSwap (nerve C) = twistedPairingNerveMap A B h hh := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change (twistedArrowOppositeSwap (nerve C)).app (Opposite.op ⦋n⦌)
    ((edgewiseWeightIso n).hom ≫ SSet.yonedaEquiv.symm
      (twistedPairingSimplex (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op) σ) ≫
        (nerveOppositeIso (C := C)).inv) =
      (edgewiseWeightIso n).hom ≫ SSet.yonedaEquiv.symm (twistedPairingSimplex A B h σ)
  rw [twistedPairingSimplex_reverse]
  exact twistedArrowOppositeSwap_nerve_reverse n (twistedPairingSimplex A B h σ)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
end

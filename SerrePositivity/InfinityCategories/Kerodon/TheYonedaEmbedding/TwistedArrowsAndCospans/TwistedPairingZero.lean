module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingProjections

/-!
概要：元の全 twisted pairing の零単体は元の実射そのもの。
方針：元の長い単体の零次の対象と射を計算し、同じ後合成を保つ。
規約：元の四角形の全自然性と同じモデル源を使い、新たな単体を選ばない。
使われ方：全 pairing の元の単位ラベルの像の計算。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)

/-- 元の長い単体の次数0は、元の実射の一単体になる。 -/
lemma twistedPairingSimplex_zero (i : I) :
    twistedPairingSimplex A B h (nerveVertex i) = ComposableArrows.mk₁ (h i) := by
  have ho : ∀ a, (twistedPairingSimplex A B h (nerveVertex i)).obj a =
      (ComposableArrows.mk₁ (h i)).obj a := by
    intro a
    fin_cases a <;> rfl
  refine CategoryTheory.Functor.ext ho ?_
  intro a b f
  have hf := leOfHom f
  fin_cases a <;> fin_cases b <;>
    simp_all [twistedPairingSimplex, twistedPairingSimplexMap, twistedPairingSimplexObj,
      twistedPairingCross, twistedPairingLeftIndex, twistedPairingRightIndex]
  all_goals rfl

/-- 元の全 pairing の零次の値は、同じ重みの表示で元の実射を読むもの。 -/
lemma twistedPairingNerveMap_zero
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) (i : I) :
    (twistedPairingNerveMap A B h hh).app (Opposite.op ⦋0⦌) (nerveVertex i) =
      (edgewiseWeightIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₁ (h i)) := by
  change (edgewiseWeightIso 0).hom ≫
    (SSet.yonedaEquiv (X := nerve C)).symm (twistedPairingSimplex A B h (nerveVertex i)) = _
  rw [twistedPairingSimplex_zero]

/-- 同じ全 pairing を任意の元の写像へ後合成しても、零次の実射を保つ。 -/
lemma twistedPairingNerveMap_zero_postcomp {D : SSet.{u}} (G : nerve C ⟶ D)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) (i : I) :
    (twistedPairingNerveMap A B h hh ≫ edgewiseSubdivisionMap G).app
      (Opposite.op ⦋0⦌) (nerveVertex i) =
      (edgewiseWeightIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₁ (h i)) ≫ G := by
  change ((twistedPairingNerveMap A B h hh).app _ (nerveVertex i)) ≫ G = _
  rw [twistedPairingNerveMap_zero, Category.assoc]
end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end

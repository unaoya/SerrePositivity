module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeEvaluation

/-!
概要：同じ長い単体を左右の標準区間へ制限すると、元の両端の射列に戻る。
方針：元の頂点座標と同じ実射を、関手の全対象・全射で照合する。
規約：IS-W2 R03dの既存の係数移送・自然性。頂点の一致だけで代用しない。
使われ方：twisted arrowへの全写像の二射影を元の両端と厳密に合わせる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 左の標準区間の全頂点は同じ左ブロックにある。 -/
theorem twistedPairingLeftOrder_lt (n : ℕ) (i : Fin (n+1)) :
    (joinLeftOrderHom n n i).val < n+1 := i.isLt

/-- 左の標準区間の同じ添字は、元の逆順の添字。 -/
theorem twistedPairingLeftIndex_order (n : ℕ) (i : Fin (n+1))
    (hi : (joinLeftOrderHom n n i).val < n+1) :
    twistedPairingLeftIndex (joinLeftOrderHom n n i) hi = i.rev := by
  apply Fin.ext
  dsimp [twistedPairingLeftIndex, joinLeftOrderHom, Fin.rev]
  omega

variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  {n : ℕ} (σ : Fin (n+1) ⥤ I)

/-- 同じ右区間への制限は、元の共変の標的の全射列。 -/
theorem twistedPairingSimplex_restrict_right :
    (joinRightOrderHom n n).monotone.functor ⋙ twistedPairingSimplex A B h σ = σ ⋙ B := by
  apply CategoryTheory.Functor.hext
  · intro i
    exact twistedPairingSimplex_obj_right A B h σ i
  · intro i j f
    have hi := twistedPairingRightVertex_not_lt n i
    have hj := twistedPairingRightVertex_not_lt n j
    change HEq (twistedPairingSimplexMap A B h σ (edgewiseRightVertex n i)
      (edgewiseRightVertex n j) ((joinRightOrderHom n n).monotone (leOfHom f))) (B.map (σ.map f))
    refine (twistedPairingSimplexMap_right_heq A B h σ _ _ _ hi hj).trans ?_
    exact twistedPairingThinMap_heq (σ ⋙ B)
      (twistedPairingRightIndex_vertex n i hi) (twistedPairingRightIndex_vertex n j hj)

/-- 同じ左区間への制限は、元の反変の始域の全射列の逆反転。 -/
theorem twistedPairingSimplex_restrict_left :
    (joinLeftOrderHom n n).monotone.functor ⋙ twistedPairingSimplex A B h σ =
      nerveUnreverseChain (σ ⋙ A) := by
  apply CategoryTheory.Functor.hext
  · intro i
    change twistedPairingSimplexObj A B σ (joinLeftOrderHom n n i) = (A.obj (σ.obj i.rev)).unop
    rw [twistedPairingSimplexObj_left A B σ _ (twistedPairingLeftOrder_lt n i),
      twistedPairingLeftIndex_order]
  · intro i j f
    have hi := twistedPairingLeftOrder_lt n i
    have hj := twistedPairingLeftOrder_lt n j
    change HEq (twistedPairingSimplexMap A B h σ (joinLeftOrderHom n n i)
      (joinLeftOrderHom n n j) ((joinLeftOrderHom n n).monotone (leOfHom f))) (A.map (σ.map (homOfLE _))).unop
    refine (twistedPairingSimplexMap_left_heq A B h σ _ _ _ hi hj).trans ?_
    exact twistedPairingThinUnopMap_heq (σ ⋙ A)
      (twistedPairingLeftIndex_order n j hj) (twistedPairingLeftIndex_order n i hi)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

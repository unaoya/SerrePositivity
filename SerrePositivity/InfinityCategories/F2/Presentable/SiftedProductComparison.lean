module

public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedInfinity
public import SerrePositivity.InfinityCategories.F2.Filtered.TotalKanProductEquivalence

/-!
概要：sifted な底上の二つの空間値 coherent 図式の、元の全空間 Kan 模型の積比較は同値。
方針：底の二項対角の cofinality を left fibration の直積で引き戻し、置換の単位を消去。
規約：元の F2 の比較射・二射影・単位を保持。底の quasicategory 性は不要。
使われ方：HTT 5.5.8.11 の空間値の二項積の交換、P_Σ の sifted 余極限での閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- sifted な底上の fiber ごとの積から全空間の積への元の二射影の組は right cofinal。 -/
lemma fiberProductToProduct_isRightCofinal_of_sifted {E D B : SSet.{u}} [IsSiftedInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    IsRightCofinal (lift (pullback.fst p q) (pullback.snd p q)) := by
  let h := F2.fiberProduct_binaryDiagonal_isPullback p q
  have hc := (isRightCofinal_of_isIso h.isoPullback.hom).comp
    (leftFibration_pullback_isRightCofinal (p ⊗ₘ q) (lift (𝟙 B) (𝟙 B))
      (IsSiftedInfinity.diagonal_rightCofinal (K := B)))
  rw [h.isoPullback_hom_fst] at hc
  exact hc

/-- sifted な底上の元の二項積比較は弱ホモトピー同値。 -/
lemma totalKanProductComparison_isWeakHomotopyEquivalence_of_sifted
    {E D B : SSet.{u}} [IsSiftedInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    IsWeakHomotopyEquivalence (F2.totalKanProductComparison p q) := by
  have hc := (fiberProductToProduct_isRightCofinal_of_sifted p q).isWeakHomotopyEquivalence
  have h := hc.comp (F2.continuousKanProductUnit_isWeakHomotopyEquivalence E D)
  rw [← F2.totalKanProductComparison_unit_product p q] at h
  exact (F2.continuousKanReplacementUnit_isWeakHomotopyEquivalence
    (pullback p q)).cancel_left h

/-- sifted な底上の元の二項積比較は、実際の単体的ホモトピー逆を持つ。 -/
lemma totalKanProductComparison_homotopyEquivalence_of_sifted
    {E D B : SSet.{u}} [IsSiftedInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    IsSimplicialHomotopyEquivalence (F2.totalKanProductComparison p q) := by
  have := kanTensor_isKan (F2.continuousKanReplacement.obj E) (F2.continuousKanReplacement.obj D)
  have h := totalKanProductComparison_isWeakHomotopyEquivalence_of_sifted p q
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits

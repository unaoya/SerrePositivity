module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingSimplex

/-!
概要：元の長い単体の両半分を、同じedgewiseの頂点座標で照合する。
方針：左の二重反転と右の平行移動を計算し、同じ対象の移送を記録する。
規約：IS-W2 R03dの座標・自然性の法則。全単体の写像はここではまだ束ねない。
使われ方：同じtwisted arrowの両端の射影と全再添字付けの検査。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open CategoryTheory

/-- 左の頂点座標は同じ左半分にある。 -/
theorem twistedPairingLeftVertex_lt (n : ℕ) (i : Fin (n+1)) :
    (edgewiseLeftVertex n i).val < n+1 := by
  dsimp [edgewiseLeftVertex]
  omega

/-- 右の頂点座標は同じ右半分にある。 -/
theorem twistedPairingRightVertex_not_lt (n : ℕ) (i : Fin (n+1)) :
    ¬ (edgewiseRightVertex n i).val < n+1 := by
  dsimp [edgewiseRightVertex]
  omega

/-- 左半分の同じ座標を二度反転すると元の添字になる。 -/
theorem twistedPairingLeftIndex_vertex (n : ℕ) (i : Fin (n+1))
    (hi : (edgewiseLeftVertex n i).val < n+1) :
    twistedPairingLeftIndex (edgewiseLeftVertex n i) hi = i := by
  apply Fin.ext
  have := i.isLt
  dsimp [twistedPairingLeftIndex, edgewiseLeftVertex]
  omega

/-- 右半分の同じ平行移動を戻すと元の添字になる。 -/
theorem twistedPairingRightIndex_vertex (n : ℕ) (i : Fin (n+1))
    (hi : ¬ (edgewiseRightVertex n i).val < n+1) :
    twistedPairingRightIndex (edgewiseRightVertex n i) hi = i := by
  apply Fin.ext
  dsimp [twistedPairingRightIndex, edgewiseRightVertex]
  omega

variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  {n : ℕ} (σ : Fin (n+1) ⥤ I)

/-- 同じ長い単体の左半分は、元の反変の始域そのもの。 -/
theorem twistedPairingSimplex_obj_left (i : Fin (n+1)) :
    (twistedPairingSimplex A B h σ).obj (edgewiseLeftVertex n i) = (A.obj (σ.obj i)).unop := by
  change twistedPairingSimplexObj A B σ (edgewiseLeftVertex n i) = _
  rw [twistedPairingSimplexObj_left A B σ _ (twistedPairingLeftVertex_lt n i),
    twistedPairingLeftIndex_vertex]

/-- 同じ長い単体の右半分は、元の共変の標的そのもの。 -/
theorem twistedPairingSimplex_obj_right (i : Fin (n+1)) :
    (twistedPairingSimplex A B h σ).obj (edgewiseRightVertex n i) = B.obj (σ.obj i) := by
  change twistedPairingSimplexObj A B σ (edgewiseRightVertex n i) = _
  rw [twistedPairingSimplexObj_right A B σ _ (twistedPairingRightVertex_not_lt n i),
    twistedPairingRightIndex_vertex]

/-- 左ブロックの同じ実射を、型の移送を消した異種等式で回収する。 -/
theorem twistedPairingSimplexMap_left_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : i.val < n+1) (hj : j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (A.map (σ.map (homOfLE (show twistedPairingLeftIndex j hj ≤ twistedPairingLeftIndex i hi
        by dsimp [twistedPairingLeftIndex]; exact Nat.sub_le_sub_left hij _)))).unop := by
  simp only [twistedPairingSimplexMap, dite_eq_left hi, dite_eq_left hj]
  exact twistedPairingTransport_heq
    (twistedPairingSimplexObj_left A B σ i hi) (twistedPairingSimplexObj_left A B σ j hj) _

/-- 交差ブロックの同じ実射を、型の移送を消した異種等式で回収する。 -/
theorem twistedPairingSimplexMap_cross_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : i.val < n+1) (hj : ¬ j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (twistedPairingCross A B h σ (twistedPairingLeftIndex i hi) (twistedPairingRightIndex j hj)) := by
  simp only [twistedPairingSimplexMap, dite_eq_left hi, dite_eq_right hj]
  exact twistedPairingTransport_heq
    (twistedPairingSimplexObj_left A B σ i hi) (twistedPairingSimplexObj_right A B σ j hj) _

/-- 右ブロックの同じ実射を、型の移送を消した異種等式で回収する。 -/
theorem twistedPairingSimplexMap_right_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : ¬ i.val < n+1) (hj : ¬ j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (B.map (σ.map (homOfLE (show twistedPairingRightIndex i hi ≤ twistedPairingRightIndex j hj
        by dsimp [twistedPairingRightIndex]; exact Nat.sub_le_sub_right hij _)))) := by
  simp only [twistedPairingSimplexMap, dite_eq_right hi]
  exact twistedPairingTransport_heq
    (twistedPairingSimplexObj_right A B σ i hi) (twistedPairingSimplexObj_right A B σ j hj) _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

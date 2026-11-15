module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingCrossNaturality

/-!
概要：同じ長い射列は、実際のedgewise重みの全再添字付けと厳密に両立する。
方針：元の左右の頂点座標で対象と実射を照合し、交差射の基点変更則を使う。
規約：IS-W2 R03dの同じ単体と自然性の法則。頂点ごとの比較で代用しない。
使われ方：全source frameの要素圏のnerveをtwisted arrowへ送る全写像。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open CategoryTheory

/-- 同じ左の添字の逆変換。 -/
theorem twistedPairingLeftVertex_index {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    edgewiseLeftVertex n (twistedPairingLeftIndex i hi) = i := by
  apply Fin.ext
  dsimp [edgewiseLeftVertex, twistedPairingLeftIndex]
  omega

/-- 同じ右の添字の逆変換。 -/
theorem twistedPairingRightVertex_index {n : ℕ} (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    edgewiseRightVertex n (twistedPairingRightIndex i hi) = i := by
  apply Fin.ext
  have := i.isLt
  dsimp [edgewiseRightVertex, twistedPairingRightIndex]
  omega

variable {m n : ℕ} (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n)

/-- 左半分での実重みの再添字付けは、元の同じ左座標で計算される。 -/
theorem twistedPairingReindex_left (i : Fin (m+m+1+1)) (hi : i.val < m+1) :
    edgewiseWeightReindexOrderHom.{u} α i =
      edgewiseLeftVertex n (α.toOrderHom (twistedPairingLeftIndex i hi)) := by
  exact (congrArg (edgewiseWeightReindexOrderHom.{u} α)
    (twistedPairingLeftVertex_index i hi).symm).trans
      (edgewiseWeightReindexOrderHom_left α _)

/-- 右半分での実重みの再添字付けは、元の同じ右座標で計算される。 -/
theorem twistedPairingReindex_right (i : Fin (m+m+1+1)) (hi : ¬ i.val < m+1) :
    edgewiseWeightReindexOrderHom.{u} α i =
      edgewiseRightVertex n (α.toOrderHom (twistedPairingRightIndex i hi)) := by
  exact (congrArg (edgewiseWeightReindexOrderHom.{u} α)
    (twistedPairingRightVertex_index i hi).symm).trans
      (edgewiseWeightReindexOrderHom_right α _)

/-- 元の左座標の添字も、同じ実重みの再添字付けで移る。 -/
theorem twistedPairingReindex_leftIndex (i : Fin (m+m+1+1)) (hi : i.val < m+1)
    (hbi : (edgewiseWeightReindexOrderHom.{u} α i).val < n+1) :
    twistedPairingLeftIndex (edgewiseWeightReindexOrderHom.{u} α i) hbi =
      α.toOrderHom (twistedPairingLeftIndex i hi) := by
  apply Fin.ext
  have hv := congrArg Fin.val (twistedPairingReindex_left.{u} α i hi)
  have hb := (α.toOrderHom (twistedPairingLeftIndex i hi)).isLt
  dsimp only [edgewiseLeftVertex, twistedPairingLeftIndex] at hv hb ⊢
  omega

/-- 元の右座標の添字も、同じ実重みの再添字付けで移る。 -/
theorem twistedPairingReindex_rightIndex (i : Fin (m+m+1+1)) (hi : ¬ i.val < m+1)
    (hbi : ¬ (edgewiseWeightReindexOrderHom.{u} α i).val < n+1) :
    twistedPairingRightIndex (edgewiseWeightReindexOrderHom.{u} α i) hbi =
      α.toOrderHom (twistedPairingRightIndex i hi) := by
  apply Fin.ext
  have hv := congrArg Fin.val (twistedPairingReindex_right.{u} α i hi)
  dsimp only [edgewiseRightVertex, twistedPairingRightIndex] at hv ⊢
  omega

variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)
  (σ : Fin (n+1) ⥤ I)

/-- 薄い添字圏の同じ両端を持つ射の像は、型の移送後も同じ実射。 -/
theorem twistedPairingThinMap_heq {D : Type u} [Category.{u} D] {N : ℕ}
    (F : Fin N ⥤ D) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f) (F.map g) := by
  subst c d
  have he : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 同じ薄い添字圏の射の反対射も、同じ実射として保持される。 -/
theorem twistedPairingThinUnopMap_heq {D : Type u} [Category.{u} D] {N : ℕ}
    (F : Fin N ⥤ Dᵒᵖ) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f).unop (F.map g).unop := by
  subst c d
  have he : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 交差射も、同じ両端の添字の移送で元の実射を保持する。 -/
theorem twistedPairingCross_heq {a b c d : Fin (n+1)} (ha : a = c) (hb : b = d) :
    HEq (twistedPairingCross A B h σ a b) (twistedPairingCross A B h σ c d) := by
  subst c d
  rfl

include hh
/-- 実際のedgewise重みの全順序射で、元の長い単体は厳密に再添字付けされる。 -/
theorem twistedPairingSimplex_reindex :
    (edgewiseWeightReindexOrderHom.{u} α).monotone.functor ⋙ twistedPairingSimplex A B h σ =
      twistedPairingSimplex A B h (α.toOrderHom.monotone.functor ⋙ σ) := by
  apply CategoryTheory.Functor.hext
  · intro i
    by_cases hi : i.val < m+1
    · dsimp only [Functor.comp_obj, Monotone.functor]
      rw [twistedPairingReindex_left.{u} α i hi, twistedPairingSimplex_obj_left]
      exact (twistedPairingSimplexObj_left A B (α.toOrderHom.monotone.functor ⋙ σ) i hi).symm
    · dsimp only [Functor.comp_obj, Monotone.functor]
      rw [twistedPairingReindex_right.{u} α i hi, twistedPairingSimplex_obj_right]
      exact (twistedPairingSimplexObj_right A B (α.toOrderHom.monotone.functor ⋙ σ) i hi).symm
  · intro i j f
    let β := edgewiseWeightReindexOrderHom.{u} α
    have hij : i ≤ j := leOfHom f
    change HEq (twistedPairingSimplexMap A B h σ (β i) (β j) (β.monotone hij))
      (twistedPairingSimplexMap A B h (α.toOrderHom.monotone.functor ⋙ σ) i j hij)
    by_cases hi : i.val < m+1
    · have hbi : (β i).val < n+1 := by
        rw [twistedPairingReindex_left.{u} α i hi]
        exact twistedPairingLeftVertex_lt _ _
      by_cases hj : j.val < m+1
      · have hbj : (β j).val < n+1 := by
          rw [twistedPairingReindex_left.{u} α j hj]
          exact twistedPairingLeftVertex_lt _ _
        have hL := twistedPairingSimplexMap_left_heq A B h σ (β i) (β j) (β.monotone hij) hbi hbj
        have hR := twistedPairingSimplexMap_left_heq A B h (α.toOrderHom.monotone.functor ⋙ σ) i j hij hi hj
        refine hL.trans (HEq.trans ?_ hR.symm)
        exact twistedPairingThinUnopMap_heq (σ ⋙ A)
          (twistedPairingReindex_leftIndex.{u} α j hj hbj)
          (twistedPairingReindex_leftIndex.{u} α i hi hbi)
      · have hbj : ¬ (β j).val < n+1 := by
          rw [twistedPairingReindex_right.{u} α j hj]
          exact twistedPairingRightVertex_not_lt _ _
        have hL := twistedPairingSimplexMap_cross_heq A B h σ (β i) (β j) (β.monotone hij) hbi hbj
        have hR := twistedPairingSimplexMap_cross_heq A B h (α.toOrderHom.monotone.functor ⋙ σ) i j hij hi hj
        refine hL.trans (HEq.trans ?_ hR.symm)
        exact (twistedPairingCross_heq A B h σ
          (twistedPairingReindex_leftIndex.{u} α i hi hbi)
          (twistedPairingReindex_rightIndex.{u} α j hj hbj)).trans
            (heq_of_eq (twistedPairingCross_reindex A B h hh σ α.toOrderHom
              (twistedPairingLeftIndex i hi) (twistedPairingRightIndex j hj)).symm)
    · have hj : ¬ j.val < m+1 := fun h => hi (lt_of_le_of_lt hij h)
      have hbi : ¬ (β i).val < n+1 := by
        rw [twistedPairingReindex_right.{u} α i hi]
        exact twistedPairingRightVertex_not_lt _ _
      have hbj : ¬ (β j).val < n+1 := by
        rw [twistedPairingReindex_right.{u} α j hj]
        exact twistedPairingRightVertex_not_lt _ _
      have hL := twistedPairingSimplexMap_right_heq A B h σ (β i) (β j) (β.monotone hij) hbi hbj
      have hR := twistedPairingSimplexMap_right_heq A B h (α.toOrderHom.monotone.functor ⋙ σ) i j hij hi hj
      refine hL.trans (HEq.trans ?_ hR.symm)
      exact twistedPairingThinMap_heq (σ ⋙ B)
        (twistedPairingReindex_rightIndex.{u} α i hi hbi)
        (twistedPairingReindex_rightIndex.{u} α j hj hbj)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

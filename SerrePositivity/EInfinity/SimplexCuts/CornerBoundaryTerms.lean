module

public import SerrePositivity.EInfinity.SimplexCuts.CornerDeletedTensors
public import SerrePositivity.EInfinity.SimplexCuts.CornerBoundarySigns

/-!
# 混合角の実際の符号付き出力境界項

Berger–Fresse §2.2.7、M14 L09a。
同じ削除面の元の実テンソルと整数符号を合わせる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C164：経路頂点の面番号で読んだ元の境界符号は同じ符号。 -/
lemma outputBoundarySign_eq_at_of_rank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) :
    outputBoundarySign s v (label s v.val k) j = outputBoundarySignAt s v k := by
  unfold outputBoundarySignAt outputBoundarySign
  rw [← vertexRank_symm_colorPositionEquiv s v k, colorPositionEquiv_symm_color, hj]

/-- C165：混合角の同じ実テンソルの符号を反転すれば、元の境界項が相殺する。 -/
lemma outputBoundaryTerm_swapSteps_of_sign {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc)
    (hs : outputBoundarySignAt (s.swapSteps a b) v b.castSucc =
      -outputBoundarySignAt s v b.castSucc) (x : S _⦋q⦌) :
    outputBoundaryTerm A S (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) jn x =
      -outputBoundaryTerm A S s v (label s v.val b.castSucc) jo x := by
  unfold outputBoundaryTerm
  rw [dite_eq_left hn, dite_eq_left ho,
    deletedCutTensor_swapSteps A S s v a b hab ho hn jo jno jn jnn x,
    outputBoundarySign_eq_at_of_rank _ _ _ jn jnn,
    outputBoundarySign_eq_at_of_rank _ _ _ jo jno, hs, neg_smul]

end SerrePositivity.EInfinity.SimplexCuts

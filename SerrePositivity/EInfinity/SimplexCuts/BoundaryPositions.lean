module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryIndex
public import Mathlib.Logic.Equiv.Sum

/-!
# 色の面の位置と経路の頂点の同値

Berger–Fresse §2.2.7、M14 L09a。
出力の色とその色の面番号を、経路の一つの頂点へまとめる。
全射語の各色のfiberは非空なので、零次の色の唯一の添字も保持される。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C21：色とその色の位置は、元の経路の一頂点と同じデータ。 -/
def colorPositionEquiv {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1)) :
    (Σ a : Fin r, Fin (outputDegree s u a + 1)) ≃ Fin (m + q + 1) :=
  (Equiv.sigmaCongrRight fun a =>
    ((colorPositions s u.val a).orderIsoOfFin (colorPositions_card_eq s u a)).toEquiv.trans
      (Equiv.subtypeEquivRight fun i => by
        simp only [colorPositions, Finset.mem_filter, Finset.mem_univ, true_and])).trans
    (Equiv.sigmaFiberEquiv (label s u.val))

lemma colorPositionEquiv_apply {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
    colorPositionEquiv s u ⟨a, j⟩ =
      (colorPositions s u.val a).orderEmbOfFin (colorPositions_card_eq s u a) j := rfl

lemma colorPositionEquiv_symm_color {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
    ((colorPositionEquiv s u).symm k).1 = label s u.val k := rfl

/-- C22：全ての出力の面の添字を、切断と削除する経路の頂点へ一括する。 -/
def outputBoundaryPositionEquiv {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
    OutputBoundaryIndex u q ≃ Σ _ : Cut (r + d) q, Fin (r + d + q + 1) :=
  Equiv.sigmaCongrRight fun s => colorPositionEquiv s (positiveWord u)

end SerrePositivity.EInfinity.SimplexCuts

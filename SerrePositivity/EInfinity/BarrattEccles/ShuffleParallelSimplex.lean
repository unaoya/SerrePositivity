module

public import SerrePositivity.EInfinity.BarrattEccles.ParallelShuffleCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.PermutationParallel
public import SerrePositivity.EInfinity.BarrattEccles.ArityDegreeTransport
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces

/-!
# shuffle 単体の並列結合則

概要：Berger–Fresse §1.1.3 の異なる入力への二つの代入を単体として比較する。
方針：並列の経路の各入力の座標の保存と置換の並列結合則を使う。
規約：中間 arity、出力 arity、鎖次数の三種類の移送を明示する。
使われ方：並列合成の二重 shuffle 和の各生成元を同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：並列の二段の shuffle 単体は添字替えで一致する（Berger–Fresse §1.1.3）。
方針：各頂点の三入力の座標を同定し、置換の並列結合則を適用する。
規約：二つの代入位置は異なり、代入する arity は0でもよい。
使われ方：並列の結合則の各項の正規化生成元を比較する。 -/
lemma shuffleSimplex_parallel_assoc (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (p q r : ℕ) (v : ShufflePath (p + q) r × ShufflePath p q)
    (x : (simplicial (m + 2)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (z : (simplicial k) _⦋r⦌) :
    (simplicialArityMap (by omega : m + n + k = m + k + n)).app _
        (shuffleSimplex (m + n) k (parallelSlot m n i j hji) v.1
          ((simplicialArityMap (by omega : m + 1 + n = m + n + 1)).app _
            (shuffleSimplex (m + 1) n i v.2 x y)) z) =
      (simplicial (m + k + n)).map
        (degreeCastMap (by omega : p + q + r = p + r + q)).op
        (shuffleSimplex (m + k) n (parallelSlot m k j i hji.symm)
          (parallelShuffleEquiv p q r v).1
          ((simplicialArityMap (by omega : m + 1 + k = m + k + 1)).app _
            (shuffleSimplex (m + 1) k j (parallelShuffleEquiv p q r v).2 x z)) y) := by
  apply (simplexEquiv (m + k + n) (p + q + r)).injective
  funext a
  simp only [simplexEquiv_arityMap, simplexEquiv_map, simplexEquiv_shuffleSimplex]
  change (finCongr (by omega : m + n + k = m + k + n)).permCongr
      (permutationComposition (m + n) k (parallelSlot m n i j hji)
        (permutationAfterInsertion m n i
          (simplexEquiv (m + 2) p x (v.2.horizontal (v.1.horizontal a)))
          (simplexEquiv n q y (v.2.vertical (v.1.horizontal a))))
        (simplexEquiv k r z (v.1.vertical a))) = _
  rw [permutationComposition_parallel_assoc, parallelShuffle_first_coordinate,
    parallelShuffle_second_coordinate, parallelShuffle_third_coordinate]
  rfl

end SerrePositivity.EInfinity.BarrattEccles

module

public import SerrePositivity.EInfinity.BarrattEccles.TripleShuffleCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.PermutationNested
public import SerrePositivity.EInfinity.BarrattEccles.ArityDegreeTransport
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces

/-!
# shuffle 単体の入れ子結合則

概要：Berger–Fresse §1.1.3 の二段の shuffle の入れ子合成を単体として比較する。
方針：三つの座標の保存と置換の入れ子結合則を各頂点で適用する。
規約：arity と鎖次数の加法の括弧はそれぞれ明示的に移送する。
使われ方：正規化鎖の shuffle 合成の入れ子結合則の各項を同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：入れ子の二段の shuffle 単体は添字替えで一致する（Berger–Fresse §1.1.3）。
方針：各頂点の三入力の座標を同定して置換の結合則を使う。
規約：等式は単体次数 p+q+r、出力 arity m+(n+k) に置く。
使われ方：shuffle 和の入れ子結合則に必要な生成元の一致を与える。 -/
lemma shuffleSimplex_nested_assoc (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (p q r : ℕ) (v : ShufflePath (p + q) r × ShufflePath p q)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial (n + 1)) _⦋q⦌)
    (z : (simplicial k) _⦋r⦌) :
    (simplicialArityMap (Nat.add_assoc m n k)).app _
        (shuffleSimplex (m + n) k (nestedSlot m n i j) v.1
          (shuffleSimplex m (n + 1) i v.2 x y) z) =
      (simplicial (m + (n + k))).map (degreeCastMap (Nat.add_assoc p q r)).op
        (shuffleSimplex m (n + k) i (tripleShuffleEquiv p q r v).1 x
          (shuffleSimplex n k j (tripleShuffleEquiv p q r v).2 y z)) := by
  apply (simplexEquiv (m + (n + k)) (p + q + r)).injective
  funext a
  simp only [simplexEquiv_arityMap, simplexEquiv_map, simplexEquiv_shuffleSimplex]
  change (finCongr (Nat.add_assoc m n k)).permCongr
      (permutationComposition (m + n) k (nestedSlot m n i j)
        (permutationComposition m (n + 1) i
          (simplexEquiv (m + 1) p x (v.2.horizontal (v.1.horizontal a)))
          (simplexEquiv (n + 1) q y (v.2.vertical (v.1.horizontal a))))
        (simplexEquiv k r z (v.1.vertical a))) = _
  rw [permutationComposition_nested_assoc, tripleShuffle_first_coordinate,
    tripleShuffle_second_coordinate, tripleShuffle_third_coordinate]
  rfl

end SerrePositivity.EInfinity.BarrattEccles

module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Simplices

/-!
# Barratt–Eccles の単体的部分合成

概要：Berger–Fresse §1.1.3 の置換の部分合成を EΣ の積上の単体集合の射にする。
方針：置換列の対応する頂点ごとに部分合成を施す。
規約：外側 arity は m+1、内側 arity は n、出力 arity は m+n。
使われ方：一般 shuffle と既存 BE 部分合成を AW の自然性により接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory
open scoped Simplicial

/-- 概要：置換列の頂点ごとの部分合成からなる単体的写像（BF §1.1.3）。
方針：codiscrete nerve の単体を置換列へ同定し各頂点で合成する。
規約：左右の入力単体の次数は等しい。
使われ方：shuffle 単体の一般の積単体からの像を与える。 -/
def simplicialPartialComposition (m n : ℕ) (i : Fin (m + 1)) :
    simplicial (m + 1) ⊗ simplicial n ⟶ simplicial (m + n) where
  app Δ := ↾fun (xy : (simplicial (m + 1)).obj Δ × (simplicial n).obj Δ) =>
    (simplexEquiv (m + n) Δ.unop.len).symm (fun j =>
    permutationComposition m n i (simplexEquiv (m + 1) Δ.unop.len xy.1 j)
      (simplexEquiv n Δ.unop.len xy.2 j))
  naturality Δ Θ f := by
    apply ConcreteCategory.hom_ext
    intro xy
    apply (simplexEquiv (m + n) Θ.unop.len).injective
    funext j
    rfl

/-- 概要：単体的部分合成の頂点公式（BF §1.1.3）。
方針：置換列の同値の往復を消す。
規約：同じ次数の二つの置換列を使う。
使われ方：shuffle 単体との一致と対角の自然性。 -/
@[simp] lemma simplexEquiv_simplicialPartialComposition (m n : ℕ) (i : Fin (m + 1))
    (q : ℕ) (x : (simplicial (m + 1)) _⦋q⦌) (y : (simplicial n) _⦋q⦌)
    (j : Fin (q + 1)) :
    simplexEquiv (m + n) q ((simplicialPartialComposition m n i).app _ (x, y)) j =
      permutationComposition m n i (simplexEquiv (m + 1) q x j) (simplexEquiv n q y j) := by
  change (simplexEquiv (m + n) q) ((simplexEquiv (m + n) q).symm _) j = _
  rw [Equiv.apply_symm_apply]

/-- 概要：一般の shuffle の積単体の像は既存の BE shuffle 単体（BF §1.1.3）。
方針：codiscrete nerve の頂点で二つの座標引き戻しを比較する。
規約：ここでは EΣ の単体なので置換列による外延性を使える。
使われ方：一般 shuffle 鎖写像と BE 部分合成の一致。 -/
lemma simplicialPartialComposition_shuffle (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    (simplicialPartialComposition m n i).app _
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex (simplicial (m + 1)) (simplicial n) s x y) =
      shuffleSimplex m n i s x y := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext j
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.simplex, simplexEquiv_simplicialPartialComposition,
    simplexEquiv_map, simplexEquiv_shuffleSimplex]
  rfl

end SerrePositivity.EInfinity.BarrattEccles

module

public import SerrePositivity.EInfinity.Operad.TensorFamily

/-!
# 有限テンソル族を二つの連続した部分へ分離する

概要：Berger–Moerdijk §1 の部分合成則で、内側の入力族と残りの入力族を分離する。
方針：後半の長さで帰納し、最後の因子の分離と結合子を使う。
規約：前半 n 個、後半 m 個の順序を保ち、空の部分を許す。
使われ方：反復合成と Schur 入力のブロック分解を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：有限テンソル族を前半 n 個と後半 m 個へ分離する同型（Berger–Moerdijk §1）。
方針：最後の因子を分離し、後半の残りを再帰で分離して結合子でまとめ直す。
規約：前半の添字は castAdd、後半の添字は natAdd で埋め込む。
使われ方：オペラッドの全入力への合成と入力族のブロック分解を接続する。 -/
def tensorFamilySplitAt : ∀ (n m : ℕ) (V : Fin (n + m) → Complex A),
    tensorFamily (n + m) V ≅
      tensorFamily n (fun j => V (j.castAdd m)) ⊗ tensorFamily m (fun j => V (j.natAdd n))
  | n, 0, V => (ρ_ (tensorFamily n (fun j => V (j.castAdd 0)))).symm
  | n, m + 1, V =>
    tensorFamilySplitLast (n + m) V ≪≫
      whiskerRightIso (tensorFamilySplitAt n m (fun j => V j.castSucc)) (V (Fin.last (n + m))) ≪≫
      (α_ (tensorFamily n (fun j => V ((j.castAdd m).castSucc)))
        (tensorFamily m (fun j => V ((j.natAdd n).castSucc))) (V (Fin.last (n + m)))) ≪≫
      whiskerLeftIso (tensorFamily n (fun j => V (j.castAdd (m + 1))))
        (tensorFamilySplitLast m (fun j => V (j.natAdd n))).symm

/-- 概要：後半が空の分離同型は右単位子の逆射となる（Berger–Moerdijk §1）。
方針：再帰の基底を評価する。
規約：前半の添字の埋め込みは castAdd 0。
使われ方：ブロック分離の自然性と合成則の空の後半の場合に使う。 -/
lemma tensorFamilySplitAt_zero (n : ℕ) (V : Fin (n + 0) → Complex A) :
    (tensorFamilySplitAt n 0 V).hom =
      (ρ_ (tensorFamily n (fun j => V (j.castAdd 0)))).inv := rfl

end SerrePositivity.EInfinity

module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitTwo
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance

/-!
模型。文献の定義との比較は後で
# 全入力への反復合成の末尾二段

概要：Berger–Moerdijk §1 の全入力への合成の末尾二入力をまとめた形へ分解する。
方針：反復合成の再帰を二回展開し、有限テンソル族の末尾二因子の分離公式を使う。
規約：最後の二つの入力の代入後にも、元の未代入入力 k 個を残す。
使われ方：全入力への合成の外側等変性で末尾二入力の交換を処理する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

/-- 概要：有限族の総和を前半と最後の二つへ分ける（Berger–Moerdijk §1）。
方針：最後の入力についての有限和の分離を二回行う。
規約：前半を二回の castSucc で指定する。
使われ方：二段の再帰から戻る arity の移送を一つにまとめる。 -/
lemma tensorFamily_sum_lastTwo (n : ℕ) (s : Fin (n + 2) → ℕ) :
    (∑ i, s i) = ((∑ i : Fin n, s i.castSucc.castSucc) + s (Fin.last n).castSucc) +
      s (Fin.last (n + 1)) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

namespace Operad

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] SerrePositivity.SymmetricSequence.level
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep CategoryTheory.eqToHom _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs

set_option maxHeartbeats 500000 in
-- 二段の再帰の arity の移送を型検査するため、この宣言だけ上限を増やす。
/-- 概要：反復合成の最後の二入力をまとめたテンソル代入で表す（Berger–Moerdijk §1）。
方針：再帰を二回展開し、終域の移送を合成した後に二段の代入の結合則を使う。
規約：最後、最後から二番目、残りの入力の順に代入する。
使われ方：任意の外側 arity の二位置への合成と全入力への反復合成を結び付ける。 -/
lemma composeFirstInputs_two_factor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin (n + 2) → ℕ) :
    P.composeFirstInputs (n + 2) k s =
      (P.arity (n + 2 + k) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n (fun i => P.arity (s i))).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
            (P.composeFirstInputInsertion (n + 1) k (s (Fin.last (n + 1))))
            (P.composeFirstInputInsertion n (k + s (Fin.last (n + 1)))
              (s (Fin.last n).castSucc)))
          (P.composeFirstInputs n ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc)
              (fun i => s i.castSucc.castSucc) ≫
            eqToHom (congrArg P.arity (by
              rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_lastTwo n s]
              omega : (∑ i : Fin n, s i.castSucc.castSucc) +
                ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc) = (∑ i, s i) + k))) := by
  let recMap := P.composeFirstInputs n
    ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc)
    (fun i => s i.castSucc.castSucc)
  let qInner := eqToHom (congrArg P.arity (by
    rw [Fin.sum_univ_castSucc]
    omega : (∑ i : Fin n, s i.castSucc.castSucc) +
      ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc) =
        (∑ i : Fin (n + 1), s i.castSucc) + (k + s (Fin.last (n + 1)))))
  let qOuter := eqToHom (congrArg P.arity (by
    rw [Fin.sum_univ_castSucc s]
    omega : (∑ i : Fin (n + 1), s i.castSucc) + (k + s (Fin.last (n + 1))) =
      (∑ i, s i) + k))
  let qTotal := eqToHom (congrArg P.arity (by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_lastTwo n s]
    omega : (∑ i : Fin n, s i.castSucc.castSucc) +
      ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc) = (∑ i, s i) + k))
  have hcast : (recMap ≫ qInner) ≫ qOuter = recMap ≫ qTotal := by
    dsimp only [qInner, qOuter, qTotal]
    rw [Category.assoc, eqToHom_trans]
  rw [P.composeFirstInputs_succ_factor (n + 1) k s,
    P.composeFirstInputs_succ_factor n (k + s (Fin.last (n + 1))) (fun i => s i.castSucc)]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_post]
  rw [hcast]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_two n (fun i => P.arity (s i))
    (R := P.arity (n + 2 + k))
    (R₁ := P.arity ((n + 1) + (k + s (Fin.last (n + 1)))))
    (R₂ := P.arity (n + ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc)))
    (O := P.arity ((∑ i, s i) + k))
    (P.composeFirstInputInsertion (n + 1) k (s (Fin.last (n + 1))))
    (P.composeFirstInputInsertion n (k + s (Fin.last (n + 1))) (s (Fin.last n).castSucc))
    (P.composeFirstInputs n ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc)
      (fun i => s i.castSucc.castSucc) ≫ eqToHom (congrArg P.arity (by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_lastTwo n s]
        omega : (∑ i : Fin n, s i.castSucc.castSucc) +
          ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc) = (∑ i, s i) + k)))

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

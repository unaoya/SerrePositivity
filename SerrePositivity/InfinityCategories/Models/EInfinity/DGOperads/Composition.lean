module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily
public import Mathlib.Algebra.BigOperators.Fin

/-!
模型。文献の定義との比較は後で
# 部分合成から全入力へのオペラッド合成

概要：Berger–Moerdijk §1 の全入力への合成射を部分合成の再帰で構成する。
方針：最後の入力から順に代入し、有限テンソル族の結合子と対称性で因子を動かす。
規約：空の内側演算族と arity 0 の演算を含める。
使われ方：Schur 対象上の自由代数の作用を生成射ごとに定義するために用いる。
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

namespace Operad

variable {A : Type u} [CommRing A]

/-- 概要：先頭 n 個の入力へ演算を代入し、末尾 k 個の入力を残す合成射（Berger–Moerdijk §1）。
方針：最後の指定入力の演算を係数の直後へ移し、部分合成してから残りへ再帰する。
規約：係数因子の移動には Koszul 対称性を使い、空の演算族は右単位子で処理する。
使われ方：k=0 として全入力へのオペラッド合成を得る。 -/
def composeFirstInputs (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : ∀ (n k : ℕ) (s : Fin n → ℕ),
    P.arity (n + k) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i)) ⟶
      P.arity ((∑ i, s i) + k)
  | 0, k, s =>
    (ρ_ (P.arity (0 + k))).hom ≫
      eqToHom (congrArg P.arity (by rw [Fin.sum_univ_zero]))
  | n + 1, k, s =>
    let l := s (Fin.last n)
    let V := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i.castSucc))
    (P.arity (n + 1 + k) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => P.arity (s i))).hom) ≫
    (P.arity (n + 1 + k) ◁ (β_ V (P.arity l)).hom) ≫
    (α_ (P.arity (n + 1 + k)) (P.arity l) V).inv ≫
    ((eqToHom (congrArg P.arity (by omega : n + 1 + k = n + k + 1)) ▷ P.arity l) ▷ V) ≫
    (P.comp (n + k) l ⟨n, by omega⟩ ▷ V) ≫
    (eqToHom (congrArg P.arity (Nat.add_assoc n k l)) ▷ V) ≫
    composeFirstInputs P n (k + l) (fun i => s i.castSucc) ≫
    eqToHom (congrArg P.arity (by
      rw [Fin.sum_univ_castSucc]
      dsimp [l]
      omega : (∑ i : Fin n, s i.castSucc) + (k + l) = (∑ i : Fin (n + 1), s i) + k))

/-- 概要：全入力に演算を代入するオペラッドの合成射（Berger–Moerdijk §1）。
方針：先頭入力への再帰的代入で未処理の末尾の入力を 0 個にする。
規約：外側 arity が 0 のときは内側の族も空で、右単位子となる。
使われ方：自由 P 代数の作用をテンソルの生成射上で構成する。 -/
def composition (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) (s : Fin n → ℕ) :
    P.arity n ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i)) ⟶ P.arity (∑ i, s i) :=
  (eqToHom (congrArg P.arity (Nat.add_zero n).symm) ▷
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫
  P.composeFirstInputs n 0 s ≫ eqToHom (congrArg P.arity (Nat.add_zero _))

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

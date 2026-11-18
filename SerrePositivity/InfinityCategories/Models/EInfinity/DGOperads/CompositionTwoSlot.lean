module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionTwoLast
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TwoLastInsertion

/-!
模型。文献の定義との比較は後で
# 反復合成の末尾二入力を二位置への合成で表す

概要：Berger–Moerdijk §1 の全入力への反復合成の末尾二段を二位置への合成射へ接続する。
方針：二段の分解に部分合成の arity の移送を適用し、係数の移送を全体の前へ移す。
規約：最後の二入力以外の前方の入力と元の未代入入力を保持する。
使われ方：反復合成の外側等変性に二位置への合成の交換則を適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] SerrePositivity.SymmetricSequence.level
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep CategoryTheory.eqToHom _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs

/-- 概要：反復合成の末尾二入力は二位置への合成と残りの反復合成に分解できる（Berger–Moerdijk §1）。
方針：末尾二段の分解と二位置への合成との比較を使い、構造射の自然性で外側の移送を移す。
規約：末尾二入力の arity を a,b、前半の有限テンソルを V と略記する。
使われ方：全入力への反復合成の外側等変性で、最後の二入力を交換する場合に用いる。 -/
lemma composeFirstInputs_twoSlot_factor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin (n + 2) → ℕ) :
    let a := s (Fin.last n).castSucc
    let b := s (Fin.last (n + 1))
    let V := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i.castSucc.castSucc))
    P.composeFirstInputs (n + 2) k s =
      (eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => P.arity (s i))) ≫
        (P.arity ((n + k) + 2) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n (fun i => P.arity (s i))).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          ((eqToHom (congrArg P.arity
              (by omega : ((n + k) + a) + b = n + ((k + b) + a))) ▷ V) ≫
            P.composeFirstInputs n ((k + b) + a) (fun i => s i.castSucc.castSucc) ≫
            eqToHom (congrArg P.arity (by
              dsimp only [a, b]
              rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_lastTwo n s]
              omega : (∑ i : Fin n, s i.castSucc.castSucc) + ((k + b) + a) =
                (∑ i, s i) + k))) := by
  dsimp only
  rw [P.composeFirstInputs_two_factor, P.composeFirstInputInsertion_two]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_first_pre, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_first_post,
    whisker_exchange_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

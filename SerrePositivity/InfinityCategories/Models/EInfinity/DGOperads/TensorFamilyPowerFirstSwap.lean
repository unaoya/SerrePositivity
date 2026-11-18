module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerTransport

/-!
模型。文献の定義との比較は後で
# 有限テンソル族の連結と先頭の隣接交換

概要：Berger–Moerdijk §1 の有限テンソル族の先頭交換と、連結した全入力の交換を比較する。
方針：先頭二ブロックの展開により、三因子の交換と二ブロックの braiding の比較へ帰着する。
規約：残りの入力ブロックの順序は保つ。
使われ方：Schur 演算の外側等変性における入力側の先頭交換を処理する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily
attribute [local irreducible] _root_.SerrePositivity.TensorPowers.power _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso

/-- 概要：三因子の先頭交換は最後の因子の射と両立する（Berger–Moerdijk §1）。
方針：三因子の独立な射に関する自然性に二つの恒等射を代入する。
規約：最後の因子の始域と終域は異なってよい。
使われ方：残りの有限族の連結を先頭交換の前へ移す。 -/
@[reassoc]
lemma tensorTripleSwapIso_naturality_tail (R S : Complex A) {T T' : Complex A}
    (f : T ⟶ T') :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso R S T).hom ≫ (S ◁ (R ◁ f)) =
      (R ◁ (S ◁ f)) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso R S T').hom := by
  simpa only [id_tensorHom] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_naturality (𝟙 R) (𝟙 S) f).symm

/-- 概要：有限族の先頭二ブロックの交換が全入力に誘導する全単射（Berger–Moerdijk §1）。
方針：二つの先頭の長さと残りの総和に分け、三ブロックの先頭交換を適用する。
規約：終域は交換後の入力族の総和である。
使われ方：テンソル冪の有限族の先頭交換の連結後の作用を記述する。 -/
def tensorFamilyFirstBlockEquiv (n : ℕ) (s : Fin (n + 2) → ℕ) :
    Fin (∑ i, s i) ≃ Fin (∑ i, s (adjacentTransposition (0 : Fin (n + 1)) i)) :=
  (finCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_two n s)).trans
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadFirstBlockSwap (s 0) (s 1) (∑ i : Fin n, s i.succ.succ)).trans
      (finCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_firstSwap n s).symm))

/-- 概要：先頭の隣接交換と有限テンソル族の連結は両立する（Berger–Moerdijk §1）。
方針：交換後の連結を展開し、残りの族の連結を自然性で移して三ブロックの比較を使う。
規約：有限族の各ブロックの長さは零でもよい。
使われ方：自由代数の外側等変性の先頭の隣接互換の場合の入力側を与える。 -/
@[reassoc]
lemma tensorPowerFamilyIso_firstSwap (K : Complex A) (n : ℕ) (s : Fin (n + 2) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso n (fun i => power K (s i))).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 2)
          (fun i => s (adjacentTransposition (0 : Fin (n + 1)) i))).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 2) s).hom ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap K (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstBlockEquiv n s) := by
  apply (cancel_mono (eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_firstSwap n s)))).1
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstBlockEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_trans,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_finCongr, Category.assoc]
  rw [eqToHom_trans]
  simp only [eqToHom_refl, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_two_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_firstSwap_transport]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_naturality_tail_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_append]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

module

public import SerrePositivity.KST.Spectra.SimplicialValueCochains

/-!
概要：全単体上の係数値 cochain の交代微分の具体式。
方針：余面の有限和を加法群の射から座標へ移し、最初の面を取り出す。
規約：退化単体への値も含む通常の非正規化 cochain。
使われ方：Goerss–Jardine VIII §2。BG と群の非斉次 cochain の微分の照合。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialValueCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全単体の係数値 cochain 微分は通常の交代面の和。
方針：加法群の射の有限和と整数倍を係数の関数へ評価する。
規約：係数は任意の加法群。
使われ方：Goerss–Jardine VIII §2。非斉次群 cochain との比較の式。 -/
lemma differential_apply (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ)
    (a : K _⦋n⦌ → M) (s : K _⦋n + 1⦌) :
    (complex K M).d n (n + 1) a s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a (K.δ i s) := by
  dsimp only [complex, AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  change (AddCommGrpCat.homAddEquiv
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (diagram K M).δ i)) a s = _
  simp only [map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (fun t : K _⦋n + 1⦌ ↦ a (K.δ i t))) s = _
  simp only [Finset.sum_apply, Pi.smul_apply]

/-- 概要：通常の cochain 微分の零番目の面を取り出した式。
方針：有限和を零と後続の添字に分ける。
規約：残る面の符号は (-1)^(j+1)。
使われ方：Goerss–Jardine VIII §2。群 cochain の作用項と積の項の比較。 -/
lemma differential_apply_succ (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ)
    (a : K _⦋n⦌ → M) (s : K _⦋n + 1⦌) :
    (complex K M).d n (n + 1) a s = a (K.δ (0 : Fin (n + 2)) s) +
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • a (K.δ j.succ s) := by
  rw [differential_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]

end

end SerrePositivity.KST.Spectra.SimplicialValueCochains

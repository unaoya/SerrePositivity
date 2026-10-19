module

public import SerrePositivity.EInfinity.IntervalCuts.InversionCounts
public import SerrePositivity.EInfinity.IntervalCuts.TensorVectors

/-!
# 色の置換と区間切断の出力

概要：Berger–Fresse §2.2.6 の切断の非退化性と全出力族を色の置換と比較する。
方針：切断点と展開位置を固定し、出力色だけを逆置換で添字替えする。
規約：σ による語の後合成は出力の k 成分を元の σ⁻¹(k) 成分へ送る。
使われ方：区間余演算の対称群等変性と Koszul 符号の比較。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open scoped BigOperators

/-- 概要：色の置換は展開後の各頂点の色へ後合成する（BF §2.2.1）。
方針：展開位置を元の語位置へ戻す定義を評価する。
規約：切断点と頂点値は固定。
使われ方：非退化性と出力 fiber の比較。 -/
lemma edgeLabel_rename {n l : ℕ} (σ : Equiv.Perm (Fin n)) (u : Fin l → Fin n)
    (p : Fin l) (q : Fin (l + 1)) :
    edgeLabel (σ ∘ u) p q = σ (edgeLabel u p q) := rfl

/-- 概要：色の置換は辺切断の非退化性を保存し反映する（BF §2.2.1）。
方針：色と頂点の対の第一成分だけに全単射を合成する。
規約：語の全射性や非退化性は不要。
使われ方：退化な切断項を両辺で同時に除く。 -/
lemma edgeNondegenerate_rename_iff {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (p : Fin l) :
    EdgeNondegenerate (σ ∘ u) p ↔ EdgeNondegenerate u p := by
  constructor
  · intro h i j hij
    have hc := congrArg Prod.fst hij
    have hv := congrArg Prod.snd hij
    exact h (Prod.ext (congrArg σ hc) hv)
  · intro h i j hij
    have hc := congrArg Prod.fst hij
    have hv := congrArg Prod.snd hij
    exact h (Prod.ext (σ.injective hc) hv)

/-- 概要：置換後の出力 fiber は逆置換で選ぶ元の fiber（BF §2.2.1）。
方針：各展開位置で色の等式に逆置換を適用する。
規約：展開位置の集合自体は変えない。
使われ方：全出力単体の置換公式。 -/
lemma edgeFiber_rename {n l : ℕ} (σ : Equiv.Perm (Fin n)) (u : Fin l → Fin n)
    (p : Fin l) (k : Fin n) :
    edgeFiber (σ ∘ u) p k = edgeFiber u p (σ.symm k) := by
  unfold edgeFiber
  apply Finset.filter_congr
  intro q _
  exact σ.eq_symm_apply.symm

/-- 概要：置換後の出力頂点集合は元の逆置換色の集合（BF §2.2.1）。
方針：fiber の一致を同じ頂点写像の像へ送る。
規約：退化切断でも成立する。
使われ方：非零項の全出力族を比較する。 -/
lemma edgeOutputVertices_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (p : Fin l) (k : Fin n) :
    edgeOutputVertices (σ ∘ u) p k = edgeOutputVertices u p (σ.symm k) := by
  rw [edgeOutputVertices, edgeFiber_rename]
  rfl

/-- 概要：置換語の辺切断の全出力族は元の族の逆置換（BF §2.2.6）。
方針：各色の非空頂点集合を比較する。
規約：語次数と切断点は固定。
使われ方：出力テンソルの Koszul 置換への接続。 -/
lemma edgeOutput_rename {n d : ℕ} (σ : Equiv.Perm (Fin n)) (u : BasisWord n d)
    (p : Fin (n + d)) :
    edgeOutput (Word.rename σ u) p = edgeOutput u p ∘ σ.symm := by
  funext k
  apply Subtype.ext
  exact edgeOutputVertices_rename σ u.val p k

/-- 概要：色の置換は切断の活動位置集合を保つ（BF §2.2.3）。
方針：区切りの条件が色の全単射に不変であることを使う。
規約：非退化切断の仮定なし。
使われ方：置換前後の逆転数を同じ位置集合で比較する。 -/
lemma activePositions_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (p : Fin l) :
    activePositions (σ ∘ u) p = activePositions u p := by
  simp only [activePositions, caesura_rename_iff]

/-- 概要：色の置換は辺切断の位置符号指数を保つ（BF §2.2.4）。
方針：各区切り条件の置換不変性を有限和に適用する。
規約：切断の退化性を制限しない。
使われ方：置換符号の比較を交換指数へ絞る。 -/
lemma edgePositionExponent_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (p : Fin l) :
    edgePositionExponent (σ ∘ u) p = edgePositionExponent u p := by
  simp only [edgePositionExponent, caesura_rename_iff]

/-- 概要：出力因子の置換はテンソルの全次数を保つ（BF §2.2.3）。
方針：再帰的な全次数を各因子の和へ戻して全単射で添字替えする。
規約：空族を含む任意の単体族。
使われ方：置換後の生成元を同じ整数成分へ置く。 -/
lemma tupleDegree_permutation (n : ℕ) (f : Fin n → Simplex) (σ : Equiv.Perm (Fin n)) :
    tupleDegree n (f ∘ σ) = tupleDegree n f := by
  simp only [tupleDegree_eq_sum, Function.comp_apply]
  exact Equiv.sum_comp σ (fun i => simplexDegree (f i))

end SerrePositivity.EInfinity.IntervalCuts

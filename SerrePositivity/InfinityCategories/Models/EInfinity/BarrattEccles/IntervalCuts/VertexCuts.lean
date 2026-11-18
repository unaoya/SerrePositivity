module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeCuts

/-!
模型。文献の定義との比較は後で
# Δ¹ の頂点の区間切断

概要：Berger–Fresse §2.2.1 の公式を一点単体へ適用する。
方針：各区間が同じ頂点を与えるため、同じ色の再出現を退化と判定する。
規約：空語は空テンソルへ作用できる。
使われ方：区間の端点が余代数射となることの基底計算。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：頂点への切断作用で全出力が非退化となる条件（BF §2.2.1）。
方針：同じ色が二度現れないことを要求する。
規約：入力頂点が零か一かには依存しない。
使われ方：正次数の語の頂点への作用を零とする。 -/
def VertexNondegenerate {n l : ℕ} (u : Fin l → Fin n) : Prop := Function.Injective u

/-- 概要：頂点への切断の退化性は有限に判定できる（BF §2.2.1）。
方針：全ての位置対の色を比較する。
規約：選択公理を使わない。
使われ方：頂点への作用の有限計算。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instDecidableVertexNondegenerate {n l : ℕ} (u : Fin l → Fin n) : Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.VertexNondegenerate u) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.VertexNondegenerate Function.Injective
  infer_instance

/-- 概要：全射語の頂点への非退化な作用は次数零に限る（BF §2.2.1）。
方針：有限集合の単射と、次数零での同じ濃度の全射を比較する。
規約：arity 零の空語も含む。
使われ方：端点への正次数の全余演算を消去する。 -/
lemma vertexNondegenerate_iff {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.VertexNondegenerate u.val ↔ d = 0 := by
  constructor
  · intro h
    have hc := Fintype.card_le_of_injective u.val h
    simp only [Fintype.card_fin] at hc
    omega
  · rintro rfl
    exact (Fintype.bijective_iff_surjective_and_card u.val).2
      ⟨u.surjective, by simp⟩ |>.1

/-- 概要：正次数の全射語の頂点への作用は必ず退化（BF §2.2.1）。
方針：非退化なら次数零という判定を使う。
規約：任意の正次数。
使われ方：端点の余代数射性を全 arity で計算する。 -/
lemma not_vertexNondegenerate_of_positive {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (hd : 0 < d) :
    ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.VertexNondegenerate u.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexNondegenerate_iff]
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

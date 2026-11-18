module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesuras

/-!
模型。文献の定義との比較は後で
# 任意の語の区切りの個数の下界

概要：Berger–Fresse §1.4.4 の table の行末と区切りを計数で比較する。
方針：最終出現位置から値への写像は単射なので、その個数は arity 以下。
規約：全射性も非退化性も仮定しない。
使われ方：長さ n+d の出力の少なくとも d 個の区切りを行末へ強制する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：最終出現位置の値の評価は単射（BF §1.2.2）。
方針：異なる二位置の同値があれば前の位置は最終出現でなくなる。
規約：任意の有限語。
使われ方：最終出現の個数を値集合の濃度で評価する。 -/
lemma finalPosition_eval_injective {n l : ℕ} (v : Fin l → Fin n) :
    Function.Injective (fun i : {i : Fin l // ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i} => v i.val) := by
  intro i j he
  apply Subtype.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact False.elim (i.property ⟨j.val, h, he.symm⟩)
  · exact h
  · exact False.elim (j.property ⟨i.val, h, he⟩)

/-- 概要：最終出現の個数は arity 以下（BF §1.2.2）。
方針：最終出現から値への単射の有限濃度を比較する。
規約：全射性は不要。
使われ方：区切りの個数の下界を得る。 -/
lemma card_final_positions_le {n l : ℕ} (v : Fin l → Fin n) :
    Fintype.card {i : Fin l // ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i} ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun i : {i : Fin l // ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i} => v i.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.finalPosition_eval_injective v)

/-- 概要：区切りは少なくとも長さから arity を引いた数だけある（BF §1.4.4）。
方針：最終出現位置と区切り位置の分割の濃度を比較する。
規約：語の長さが arity より短い場合は零の下界。
使われ方：行末以外に区切りがない table で全行末の再出現を強制する。 -/
lemma card_caesuras_ge {n l : ℕ} (v : Fin l → Fin n) :
    l - n ≤ Fintype.card {i : Fin l // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i} := by
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.card_final_positions_le v
  have hc := Fintype.card_subtype_compl (fun i : Fin l => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i)
  simp only [Fintype.card_fin] at hc
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

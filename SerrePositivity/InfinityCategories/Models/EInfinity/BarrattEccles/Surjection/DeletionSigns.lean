module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesuras

/-!
模型。文献の定義との比較は後で
# Surjection の削除微分の符号

概要：Berger–Fresse §1.2.3 の符号を、区切り位置の交代符号と直前の同値の出現で表す。
方針：区切りではそれ以前の区切りの個数を指数とし、最終出現では直前の符号を反転する。
規約：一度しか現れない値の削除係数は零とする。
使われ方：χ の削除微分を有限和で定義し、TR の鎖写像性を検証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：位置より前の区切りの個数（BF §1.2.3）。
方針：区切りであって指定位置より小さいものを数える。
規約：位置自身は含めない。
使われ方：区切りの交代符号の指数となる。 -/
def caesuraRank {n l : ℕ} (u : Fin l → Fin n) (i : Fin l) : ℕ :=
  (Finset.univ.filter (fun j => j < i ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u j)).card

/-- 概要：指定位置より前にある同じ値の出現集合（BF §1.2.3）。
方針：位置の順序と文字の一致で有限集合を切り出す。
規約：位置自身を除く。
使われ方：最終出現の直前の符号を復元する。 -/
def previousOccurrences {n l : ℕ} (u : Fin l → Fin n) (i : Fin l) : Finset (Fin l) :=
  Finset.univ.filter (fun j => j < i ∧ u j = u i)

/-- 概要：語の指定文字を削除する整数係数（BF §1.2.3）。
方針：区切りは + から交代、最後の出現は直前の同じ値の符号を反転する。
規約：一度しか現れない値では係数を零とし、非全射な削除項を省く。
使われ方：符号付き削除の和を任意の可換環へ整数係数から移す。 -/
def deletionCoefficient {n l : ℕ} (u : Fin l → Fin n) (i : Fin l) : ℤ :=
  if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i then (-1) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u i
  else if h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i).Nonempty then
    -((-1) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i).max' h)) else 0

/-- 概要：値の置換は区切りの順序番号を保つ（BF §1.2.3）。
方針：区切り位置の集合が同じであることを使う。
規約：語の位置は変えない。
使われ方：削除微分の符号の同変性を示す。 -/
lemma caesuraRank_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (i : Fin l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank (σ ∘ u) i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_rename_iff]

/-- 概要：値の置換は前の同値の出現集合を保つ（BF §1.2.3）。
方針：文字の一致を置換の単射性で比較する。
規約：集合は位置の集合として厳密に同じ。
使われ方：最終出現の削除符号の同変性を示す。 -/
lemma previousOccurrences_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (i : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (σ ∘ u) i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Function.comp_apply, Equiv.apply_eq_iff_eq]

/-- 概要：値の置換は全ての削除係数を保つ（BF §1.2.3）。
方針：区切り、順序番号、前の出現集合の保存を使う。
規約：任意の語に適用する。
使われ方：微分の Σ_n 同変性を得る。 -/
lemma deletionCoefficient_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (i : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (σ ∘ u) i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_rename_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences_rename,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank_rename]

/-- 概要：区切りの削除係数は交代符号（BF §1.2.3）。
方針：削除係数の最初の分岐を評価する。
規約：最初の区切りは +1。
使われ方：表の行に沿って微分の符号を比較する。 -/
lemma deletionCoefficient_of_caesura {n l : ℕ} (u : Fin l → Fin n) (i : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u i = (-1) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient, ite_eq_left h]

/-- 概要：直前の同じ値の出現は区切りである（BF §1.2.3）。
方針：最大の前の出現にも指定位置で同じ値が再び現れる。
規約：指定位置は最終出現でなくてもよい。
使われ方：最終出現の係数を前の出現の係数で表す。 -/
lemma caesura_previousOccurrence {n l : ℕ} (u : Fin l → Fin n) (i : Fin l)
    (h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i).max' h) := by
  have hm := Finset.max'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i) h
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  exact ⟨i, hm.1, hm.2.symm⟩

/-- 概要：最後の出現の符号は直前の同じ値の符号と逆（BF §1.2.3）。
方針：直前の出現が区切りであることと削除係数の第二分岐を使う。
規約：前の出現があるときだけ主張する。
使われ方：原典の符号規約と定義の一致を保証する。 -/
lemma deletionCoefficient_final {n l : ℕ} (u : Fin l → Fin n) (i : Fin l)
    (hi : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) (h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u i =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i).max' h) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura u _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_previousOccurrence u i h)]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient, ite_eq_right hi, dite_eq_left h]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

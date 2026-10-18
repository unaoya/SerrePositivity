module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign

/-!
# shuffle の二つの辺数の等式による移送

概要：Berger–Fresse §1.1.3 の反復 shuffle の入力辺数の等式を扱う。
方針：辺数の等式を消去して恒等同値を用いる。
規約：辺集合の位置とその順序は変えない。
使われ方：第二・第三入力の交換に伴う外側の経路の型を合わせる。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：二つの辺数の等式で shuffle の経路を移送する（Berger–Fresse §1.1.3）。
方針：両方の等式を消去する。
規約：入力の辺数はそれぞれ独立に移送できる。
使われ方：三入力の二つの括弧付けと入力交換を組み合わせる。 -/
def shufflePathCastEquiv {p q r s : ℕ} (hp : p = r) (hq : q = s) :
    ShufflePath p q ≃ ShufflePath r s := by
  subst r s
  exact Equiv.refl _

/-- 概要：辺数の移送は shuffle の符号を保つ（Berger–Fresse §1.1.3）。
方針：等式を消去する。
規約：shuffle 置換の signature を比較する。
使われ方：並列結合則の外側の経路の符号を同定する。 -/
@[simp] lemma shufflePathCastEquiv_sign {p q r s : ℕ} (hp : p = r) (hq : q = s)
    (v : ShufflePath p q) : (shufflePathCastEquiv hp hq v).sign = v.sign := by
  subst r s
  rfl

/-- 概要：辺数の移送は水平座標を保つ（Berger–Fresse §1.1.3）。
方針：両方の辺数の等式を消去する。
規約：全頂点と水平座標の型を同時に移送する。
使われ方：並列結合則の最初の入力の頂点を比較する。 -/
lemma shufflePathCastEquiv_horizontal {p q r s : ℕ} (hp : p = r) (hq : q = s)
    (v : ShufflePath p q) (a : Fin (p + q + 1)) :
    (shufflePathCastEquiv hp hq v).horizontal
        (Fin.cast (by omega : p + q + 1 = r + s + 1) a) =
      Fin.cast (congrArg (fun n => n + 1) hp) (v.horizontal a) := by
  subst r s
  rfl

/-- 概要：辺数の移送は垂直座標を保つ（Berger–Fresse §1.1.3）。
方針：両方の辺数の等式を消去する。
規約：全頂点と垂直座標の型を同時に移送する。
使われ方：並列結合則の内側の二入力の頂点を比較する。 -/
lemma shufflePathCastEquiv_vertical {p q r s : ℕ} (hp : p = r) (hq : q = s)
    (v : ShufflePath p q) (a : Fin (p + q + 1)) :
    (shufflePathCastEquiv hp hq v).vertical
        (Fin.cast (by omega : p + q + 1 = r + s + 1) a) =
      Fin.cast (congrArg (fun n => n + 1) hq) (v.vertical a) := by
  subst r s
  rfl

end SerrePositivity.EInfinity.BarrattEccles

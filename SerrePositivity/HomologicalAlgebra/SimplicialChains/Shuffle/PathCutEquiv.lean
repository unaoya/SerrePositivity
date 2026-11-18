module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.PathJoin

/-!
# 切断付き shuffle 経路の添字替え

概要：Berger–Fresse §1.1.4 の切断付き経路と二つの切断座標・二経路との全単射を構成する。
方針：連結で切断座標と前半・後半経路を回収し、依存する二次数の等式を明示する。
規約：全射性・単射性とも実際の辺集合の等式から証明する。
使われ方：AW 対角と shuffle の有限和の添字替え。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.SerrePositivity.EInfinity.BarrattEccles

private lemma path_heq_of_mem {a b c d : ℕ} (s : ShufflePath a b) (t : ShufflePath c d)
    (ha : a = c) (hb : b = d)
    (hmem : ∀ i : Fin (a + b), i ∈ s.val ↔ Fin.cast (by omega : a + b = c + d) i ∈ t.val) :
    HEq s t := by
  subst c d
  apply heq_of_eq
  apply Subtype.ext
  ext i
  exact hmem i

/-- 概要：連結後の前半経路は指定した経路を回収する（Berger–Fresse §1.1.4）。
方針：切断座標の回収と辺の所属条件を使う。
規約：二次数が依存するため異種等式で述べる。
使われ方：分割の全単射の右逆性の前半。 -/
lemma frontPath_joinPath_heq {p q : ℕ} (d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q) :
    HEq (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d) (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d)) d.2.2.1 := by
  have hh := congrArg Fin.val (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_horizontal_cut d)
  have hv := congrArg Fin.val (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_vertical_cut d)
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.path_heq_of_mem _ _ hh hv
  intro i
  change i ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin d.2.2.1.val d.2.2.2.val (by omega)) 0
      (((_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d).horizontal (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d)).val + ((_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d).vertical (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d)).val)
      (by omega) ↔ Fin.cast (by omega) i ∈ d.2.2.1.val
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval, _root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin]
  have hi : 0 + i.val < d.1.val + d.2.1.val := by omega
  rw [dite_eq_left hi]
  have he : (⟨0 + i.val, hi⟩ : Fin (d.1.val + d.2.1.val)) = Fin.cast (by omega) i := by
    apply Fin.ext
    dsimp
    omega
  rw [he]

/-- 概要：連結後の後半経路は指定した経路を回収する（Berger–Fresse §1.1.4）。
方針：切断点以後の番号の加算と減算を消し、辺の所属を比較する。
規約：補った二次数が依存するため異種等式で述べる。
使われ方：分割の全単射の右逆性の後半。 -/
lemma backPath_joinPath_heq {p q : ℕ} (d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q) :
    HEq (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d) (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d)) d.2.2.2 := by
  have hh := congrArg Fin.val (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_horizontal_cut d)
  have hv := congrArg Fin.val (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_vertical_cut d)
  have hk : (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d).val = d.1.val + d.2.1.val := rfl
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.path_heq_of_mem _ _ (by omega) (by omega)
  intro i
  change i ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin d.2.2.1.val d.2.2.2.val (by omega)) (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d).val
      ((p - ((_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d).horizontal (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d)).val) +
        (q - ((_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d).vertical (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d)).val)) (by omega) ↔
      Fin.cast (by omega) i ∈ d.2.2.2.val
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval, _root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin]
  have hi : ¬(_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d).val + i.val < d.1.val + d.2.1.val := by omega
  rw [dite_eq_right hi]
  have he : (⟨(_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d).val + i.val - (d.1.val + d.2.1.val), by omega⟩ :
      Fin ((p - d.1.val) + (q - d.2.1.val))) = Fin.cast (by omega) i := by
    apply Fin.ext
    dsimp
    omega
  rw [he]

private lemma pathCutData_ext {p q : ℕ} {u v : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q}
    (hh : u.1 = v.1) (hv : u.2.1 = v.2.1)
    (hf : HEq u.2.2.1 v.2.2.1) (hb : HEq u.2.2.2 v.2.2.2) : u = v := by
  rcases u with ⟨r, t, f, b⟩
  rcases v with ⟨r', t', f', b'⟩
  cases hh
  cases hv
  cases hf
  cases hb
  rfl

/-- 概要：切断付き経路と二つの切断座標・二経路との全単射（Berger–Fresse §1.1.4）。
方針：経路を区間へ制限し、逆方向で辺集合を連結する。
規約：切断点は始端・終端を含み、零次数の経路も扱う。
使われ方：一般の shuffle の AW 余代数射性の有限和の添字替え。 -/
def pathCutEquiv (p q : ℕ) :
    ShufflePath p q × Fin (p + q + 1) ≃ _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q where
  toFun v := _root_.SerrePositivity.SimplicialChains.Shuffle.splitPath v.1 v.2
  invFun d := (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d, _root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d)
  left_inv v := by
    apply Prod.ext
    · exact _root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_splitPath v.1 v.2
    · apply Fin.ext
      exact v.1.coordinate_sum v.2
  right_inv d := by
    apply _root_.SerrePositivity.SimplicialChains.Shuffle.pathCutData_ext
    · exact _root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_horizontal_cut d
    · exact _root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_vertical_cut d
    · exact _root_.SerrePositivity.SimplicialChains.Shuffle.frontPath_joinPath_heq d
    · exact _root_.SerrePositivity.SimplicialChains.Shuffle.backPath_joinPath_heq d

/-- 概要：連結した経路を指定した切断点で分割すると元のデータ（BF §1.1.4）。
方針：分割の全単射の右逆性を適用する。
規約：二つの切断座標と前後経路を依存対の等式で回収する。
使われ方：有限和の添字替え後のテンソル項の簡約。 -/
@[simp] lemma splitPath_joinPath {p q : ℕ} (d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.splitPath (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d) (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d) = d :=
  (_root_.SerrePositivity.SimplicialChains.Shuffle.pathCutEquiv p q).right_inv d

end SerrePositivity.SimplicialChains.Shuffle

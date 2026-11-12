module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSumNaturality

/-!
概要：三因子の join の中区間と、二重に制限した単体作用を比較する。
方針：二つの切断の逆像の間の区間を直接定義し、順序写像の各値を比較する。
規約：空区間を許し、頂点数の移送は HEq で明示する。
使われ方：HTT §1.2.8、4.2.4.1 と Kerodon 7.4.1.6（Tag 05QS） の反復 slice の再結合。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：順序写像を三因子の join の中区間に制限する。
方針：始域と終域で前の切断を引き、二つの切断の間の頂点を対応させる。
規約：中区間は終域の [a,a+b)、始域の二つの逆像の間。
使われ方：Kerodon §4.3.5（Tag 017V） の再結合での中因子の作用。 -/
def joinMiddleMap {m n : ℕ} (α : Fin m →o Fin n) (a b : ℕ) :
    Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a) →o Fin b where
  toFun i := by
    let j : Fin m := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val, by
      have := i.isLt
      have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (a + b)
      omega⟩
    have hj : a ≤ (α j).val := by
      apply Nat.le_of_not_lt
      intro ha
      have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α a j).mpr ha
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a at hi
      omega
    have hk : (α j).val < a + b := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α (a + b) j).mp
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b)
      have := i.isLt
      omega
    exact ⟨(α j).val - a, by omega⟩
  monotone' i j h := Nat.sub_le_sub_right (α.monotone (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + j.val
    omega)) a

/-- 概要：同じ頂点の値を持つ制限写像は、頂点数の移送後にも同じ補った単体作用を与える。
方針：頂点数の等式で置換し、順序写像の外延性と HEq の反映を使う。
規約：始域・終域の双方の頂点数が異なる表記の場合を扱う。
使われ方：HTT §1.2.8 の三つの区間の制限写像の比較。 -/
lemma joinAugMap_heq (X : SSet.{u}) {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (α : Fin m →o Fin n) (β : Fin m' →o Fin n')
    (hα : ∀ (i : Fin m) (j : Fin m'), i.val = j.val → (α i).val = (β j).val)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X n) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X n') (hxy : HEq x y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X α x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X β y) := by
  subst m' n'
  have h : α = β := by
    ext i
    exact hα i i rfl
  subst β
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X α) (eq_of_heq hxy) |>.heq

/-- 概要：三因子の長さの和表示は各区間の長さと単体で一意に決まる。
方針：部分型の値を比較し、三つの長さで置換した後に各単体の HEq を等式に戻す。
規約：全頂点数の和の証明の選択には依存しない。
使われ方：Kerodon §4.3.5（Tag 017V） の再結合と単体作用の可換性の外延性。 -/
lemma joinTripleSimplex_ext {A B C : SSet.{u}} {n : ℕ}
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinTripleSimplex A B C n)
    (ha : s.val.1 = t.val.1) (hb : s.val.2.1 = t.val.2.1)
    (hc : s.val.2.2.1 = t.val.2.2.1)
    (hx : HEq s.val.2.2.2.1 t.val.2.2.2.1)
    (hy : HEq s.val.2.2.2.2.1 t.val.2.2.2.2.1)
    (hz : HEq s.val.2.2.2.2.2 t.val.2.2.2.2.2) : s = t := by
  rcases s with ⟨⟨a, b, c, x, y, z⟩, h⟩
  rcases t with ⟨⟨a', b', c', x', y', z'⟩, h'⟩
  dsimp only at ha hb hc hx hy hz
  subst a' b' c'
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hz
  rfl

/-- 概要：左区間のさらに左への制限は、元の前の切断への制限と同じ単体作用。
方針：二つの切断の計算で始域を合わせ、順序写像の値が α の同じ値になることを使う。
規約：終域の切断は a と a+b。
使われ方：HTT §1.2.8 の左括弧の第一因子の自然性。 -/
lemma joinAugMap_left_left (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X a) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (a + b)) a) x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α a) x) := by
  apply joinAugMap_heq X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_leftMap α (Nat.le_add_right a b)) rfl _ _ _ _ _ HEq.rfl
  intro i j hij
  change (α ⟨i.val, _⟩).val = (α ⟨j.val, _⟩).val
  exact congrArg (fun k : Fin m ↦ (α k).val) (Fin.ext hij)

/-- 概要：左区間の右への制限は、中区間への直接の制限と同じ単体作用。
方針：前の切断の逆像を同定し、原点を引いた α の値を比較する。
規約：中因子の頂点数 b を (a+b)-a と同定してから作用させる。
使われ方：HTT §1.2.8 の左括弧の中因子の自然性。 -/
lemma joinAugMap_right_left (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X b) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (a + b)) a)
      (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X) (by omega : b = a + b - a)) x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (joinMiddleMap α a b) x) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_leftMap α (Nat.le_add_right a b)
  apply joinAugMap_heq X (by omega) (by omega) _ _ _ _ _ (by simp)
  intro i j hij
  change (α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (a + b)) a + i.val, _⟩).val - a =
    (α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + j.val, _⟩).val - a
  apply congrArg (fun k : Fin m ↦ (α k).val - a)
  exact Fin.ext (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (a + b)) a + i.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + j.val
    omega)

/-- 概要：右区間の左への制限は、中区間への直接の制限と同じ単体作用。
方針：右区間で引き戻した切断を二つの逆像の差として同定する。
規約：空の中区間も含む。
使われ方：HTT §1.2.8 の右括弧の中因子の自然性。 -/
lemma joinAugMap_left_right (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X b) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b) x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (joinMiddleMap α a b) x) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a := by
    simpa only [Nat.add_sub_cancel_left] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_rightMap α (Nat.le_add_right a b)
  apply joinAugMap_heq X hp rfl _ _ _ _ _ HEq.rfl
  intro i j hij
  change (α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val, _⟩).val - a =
    (α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + j.val, _⟩).val - a
  apply congrArg (fun k : Fin m ↦ (α k).val - a)
  exact Fin.ext (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + j.val
    omega)

/-- 概要：右区間のさらに右への制限は、後の切断からの直接の制限と同じ単体作用。
方針：二つの原点移動と逆像の差をまとめ、α の評価する頂点の値を一致させる。
規約：入力単体の長さは n-(a+b)。
使われ方：HTT §1.2.8 の右括弧の第三因子の自然性。 -/
lemma joinAugMap_right_right (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X (n - (a + b))) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b)
      (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X) (by omega : n - (a + b) = n - a - b)) x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α (a + b)) x) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a := by
    simpa only [Nat.add_sub_cancel_left] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_rightMap α (Nat.le_add_right a b)
  have hab := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_mono α (Nat.le_add_right a b)
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (a + b)
  apply joinAugMap_heq X (by omega) (by omega) _ _ _ _ _ (by simp)
  intro i j hij
  let v : Fin m := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a +
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b + i.val), by have := i.isLt; omega⟩
  let w : Fin m := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) + j.val, by have := j.isLt; omega⟩
  change (α v).val - a - b = (α w).val - (a + b)
  have hv : v = w := Fin.ext (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b + i.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) + j.val
    omega)
  rw [hv]
  omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

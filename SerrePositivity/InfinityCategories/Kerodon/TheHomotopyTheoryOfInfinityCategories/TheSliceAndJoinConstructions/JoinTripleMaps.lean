module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTripleCoordinates

/-!
概要：三つの区間による join の共通表示に単体作用を定める。
方針：二つの切断の逆像と中区間の直接の制限を使い、両括弧付けからの作用を比較する。
規約：空区間を含む全ての頂点数を扱う。
使われ方：HTT §1.2.8、4.2.4.1 と Kerodon 7.4.1.6（Tag 05QS） の反復 slice の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：二因子の和表示の等式から左因子の単体の HEq を得る。
方針：等式で置換して反射性を使う。
規約：長さの表記の違いは HEq に含める。
使われ方：Kerodon §4.3.5（Tag 017V） の再結合での各因子の比較。 -/
lemma joinSumSimplex_left_heq {A B : SSet.{u}} {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n} (h : s = t) : HEq s.val.2.2.1 t.val.2.2.1 := by
  cases h
  rfl

/-- 概要：二因子の和表示の等式から右因子の単体の HEq を得る。
方針：等式で置換して反射性を使う。
規約：長さの移送を省略せず HEq で表す。
使われ方：Kerodon §4.3.5（Tag 017V） の再結合での各因子の比較。 -/
lemma joinSumSimplex_right_heq {A B : SSet.{u}} {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n} (h : s = t) : HEq s.val.2.2.2 t.val.2.2.2 := by
  cases h
  rfl

/-- 概要：全頂点数の移送は、join の和表示の長さと単体の族を変えない。
方針：頂点数の等式で置換する。
規約：部分型の和の証明ではなく値の等式を述べる。
使われ方：HTT §1.2.8 の右括弧の残りの頂点数の移送。 -/
lemma augmentedJoinSumEquiv_cast_val (A B : SSet.{u}) {n n' : ℕ} (h : n = n')
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n'
      (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B)) h) s)).val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n s).val := by
  subst n'
  rfl

/-- 概要：三つの区間による共通表示の単体作用。
方針：先頭区間と中区間の終端の逆像を取り、左右と中区間の制限で各単体を引き戻す。
規約：入力の各区間の長さの和は n、出力は m。
使われ方：Kerodon §4.3.5（Tag 017V） の join の結合の単体的自然性。 -/
def joinTripleSimplexMap (A B C : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinTripleSimplex A B C n → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinTripleSimplex A B C m := by
  rintro ⟨⟨a, b, c, x, y, z⟩, h⟩
  change a + b + c = n at h
  refine ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a,
    m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α a) x,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap B (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMiddleMap α a b) y,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α (a + b))
      (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C) (by omega : c = n - (a + b))) z)⟩, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a) +
    (m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b)) = m
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_mono α (Nat.le_add_right a b)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (a + b)
  omega

/-- 概要：左括弧の単体作用を共通表示へ移すと三つの区間の直接の作用になる。
方針：二因子の自然性で内側の join を展開し、各区間の制限の HEq を使う。
規約：共通表示から左括弧へ戻して作用させた実際の合成を比較する。
使われ方：HTT §1.2.8 の join の結合の自然性の左側。 -/
lemma joinTripleSimplexMap_left (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinTripleSimplex A B C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftJoinSumTripleEquiv A B C m
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSumSimplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C α ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftJoinSumTripleEquiv A B C n).symm t)) =
      joinTripleSimplexMap A B C α t := by
  rcases t with ⟨⟨a, b, c, x, y, z⟩, h⟩
  change a + b + c = n at h
  subst n
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B (a + b) := ⟨⟨a, b, x, y⟩, rfl⟩
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (a + b)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augmentedJoinSumEquiv_map A B β ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B (a + b)).symm s)
  rw [Equiv.apply_symm_apply] at he
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_leftMap α (Nat.le_add_right a b)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinTripleSimplex_ext
  · exact (congrArg (fun q ↦ q.val.1) he).trans hp
  · exact (congrArg (fun q ↦ q.val.2.1) he).trans
      (congrArg (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) - k) hp)
  · rfl
  · exact (joinSumSimplex_left_heq he).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAugMap_left_left A α a b x)
  · exact (joinSumSimplex_right_heq he).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAugMap_right_left B α a b y)
  · rfl

/-- 概要：右括弧の単体作用を共通表示へ移すと三つの区間の直接の作用になる。
方針：残りの全頂点数を移送して内側の join を展開し、原点移動の制限の式を使う。
規約：共通表示から右括弧へ戻す合成について、空区間も含めて証明する。
使われ方：HTT §1.2.8 の join の結合の自然性の右側。 -/
lemma joinTripleSimplexMap_right (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinTripleSimplex A B C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightJoinSumTripleEquiv A B C m
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSumSimplexMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) α ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightJoinSumTripleEquiv A B C n).symm t)) =
      joinTripleSimplexMap A B C α t := by
  rcases t with ⟨⟨a, b, c, x, y, z⟩, h⟩
  change a + b + c = n at h
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex B C (b + c) := ⟨⟨b, c, y, z⟩, rfl⟩
  let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv B C (b + c)).symm s
  have hd : b + c = n - a := by omega
  let v' := cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C)) hd) v
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv B C (n - a) v' =
      (⟨⟨b, c, y, z⟩, by change b + c = n - a; omega⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex B C (n - a)) := by
    apply Subtype.ext
    exact (augmentedJoinSumEquiv_cast_val B C hd v).trans
      (congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv B C (b + c)).apply_symm_apply s))
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augmentedJoinSumEquiv_map B C (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) v'
  rw [hv] at he
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b) - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a := by
    simpa only [Nat.add_sub_cancel_left] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_rightMap α (Nat.le_add_right a b)
  have hab := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPullCut_mono α (Nat.le_add_right a b)
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (a + b)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinTripleSimplex_ext
  · rfl
  · exact (congrArg (fun q ↦ q.val.1) he).trans hp
  · have hc := congrArg (fun q ↦ q.val.2.1) he
    exact hc.trans (by
      change (m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a) - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b =
        m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (a + b)
      omega)
  · rfl
  · exact (joinSumSimplex_left_heq he).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAugMap_left_right B α a b y)
  · have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAugMap_right_right C α a b
      (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C) (by omega : c = n - (a + b))) z)
    apply (joinSumSimplex_right_heq he).trans
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) b)
      (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C) (by omega : c = n - a - b)) z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α (a + b))
        (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C) (by omega : c = n - (a + b))) z))
    simpa only [cast_cast] using hr

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyLimitsJoinAssociator

/-!
概要：join の結合同型が三因子の射に関して自然であることを証明する。
方針：長さの和表示では各長さを保ち、各因子の補った単体に射を作用させる。
規約：因子の射に単射性・同値性・Kan 性を要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の反復 slice のパラメータ変更。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：二因子の和表示に各因子の射を作用させる。
方針：左右の頂点数を保ち、補った単体の射を両因子に適用する。
規約：全頂点数も保持する。
使われ方：Kerodon §4.3.5（Tag 017V） の join の結合と joinMap の整合性。 -/
def joinSumSimplexHom {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A' B' n
  | ⟨⟨a, b, x, y⟩, h⟩ => ⟨⟨a, b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f a x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom g b y⟩, h⟩

/-- 概要：join の和表示への全単射は両因子の射の作用と可換。
方針：空の場合を分け、非空では joinMap の各次数の定義を読む。
規約：因子の射に追加の仮定は不要。
使われ方：HTT §1.2.8 の結合同型の自然性の準備。 -/
lemma augmentedJoinSumEquiv_hom {A A' B B' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A' B' n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) n s) =
      joinSumSimplexHom f g n (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n s) := by
  cases n with
  | zero => rfl
  | succ n =>
    rcases s with ⟨a, x, y⟩
    rfl

/-- 概要：三つの区間の共通表示に各因子の射を作用させる。
方針：三つの頂点数とその和を保ち、補った各単体を写す。
規約：空の因子では唯一の補った単体を保つ。
使われ方：Kerodon §4.3.5（Tag 017V） の再結合と各因子の写像の比較。 -/
def joinTripleSimplexHom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinTripleSimplex A B C n → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinTripleSimplex A' B' C' n
  | ⟨⟨a, b, c, x, y, z⟩, hn⟩ =>
    ⟨⟨a, b, c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f a x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom g b y, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom h c z⟩, hn⟩

/-- 概要：左括弧の和表示の展開は各因子の射と可換。
方針：内側の二因子の自然性を、三つの区間への値の写像へ渡す。
規約：部分型の和の証明は外延性で分離する。
使われ方：HTT §1.2.8 の左括弧の自然性。 -/
lemma leftJoinSumTripleEquiv_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftJoinSumTripleEquiv A' B' C' n (joinSumSimplexHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) h n s) =
      joinTripleSimplexHom f g h n (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftJoinSumTripleEquiv A B C n s) := by
  rcases s with ⟨⟨r, c, t, z⟩, hn⟩
  apply Subtype.ext
  exact congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A' B' r ↦
    (⟨q.val.1, q.val.2.1, c, q.val.2.2.1, q.val.2.2.2, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom h c z⟩ :
      Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A' a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B' b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C' c))
    (augmentedJoinSumEquiv_hom f g r t)

/-- 概要：右括弧の和表示の展開は各因子の射と可換。
方針：内側の右の join の自然性を共通表示の値へ移す。
規約：三つの区間の長さを変えず、単体だけを写す。
使われ方：HTT §1.2.8 の右括弧の自然性。 -/
lemma rightJoinSumTripleEquiv_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightJoinSumTripleEquiv A' B' C' n (joinSumSimplexHom f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g h) n s) =
      joinTripleSimplexHom f g h n (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightJoinSumTripleEquiv A B C n s) := by
  rcases s with ⟨⟨a, r, x, t⟩, hn⟩
  apply Subtype.ext
  exact congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex B' C' r ↦
    (⟨a, q.val.1, q.val.2.1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f a x, q.val.2.2.1, q.val.2.2.2⟩ :
      Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A' a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B' b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C' c))
    (augmentedJoinSumEquiv_hom g h r t)

/-- 概要：左括弧の補った単体の共通表示は三因子の射と可換。
方針：外側の join の和表示と内側の展開の自然性を合成する。
規約：全頂点数零も含む。
使われ方：Kerodon §4.3.5（Tag 017V） の結合同型の自然性。 -/
lemma leftJoinTripleEncoding_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A' B' C' n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) h) n s) =
      joinTripleSimplexHom f g h n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A B C n s) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftJoinSumTripleEquiv A' B' C' n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A' B') C' n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) h) n s)) = _
  rw [augmentedJoinSumEquiv_hom, leftJoinSumTripleEquiv_hom]
  rfl

/-- 概要：右括弧の補った単体の共通表示は三因子の射と可換。
方針：外側の join の和表示と右因子の展開の自然性を合成する。
規約：三因子の射の全次数での作用を比較する。
使われ方：Kerodon §4.3.5（Tag 017V） の結合同型の自然性。 -/
lemma rightJoinTripleEncoding_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C)) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A' B' C' n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g h)) n s) =
      joinTripleSimplexHom f g h n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C n s) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightJoinSumTripleEquiv A' B' C' n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B' C') n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g h)) n s)) = _
  rw [augmentedJoinSumEquiv_hom, rightJoinSumTripleEquiv_hom]
  rfl

/-- 概要：join の結合同型は三つの因子の射について自然。
方針：各次数で右括弧の共通表示を使って検出し、両側の表示の自然性で比較する。
規約：因子の射に単射性や同値性を要求しない。
使われ方：HTT 4.2.4.1 の反復 slice のパラメータ変更と固定面の整合性。 -/
lemma joinAssociator_naturality {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A' B' C').hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g h) := by
  have he (A B C : SSet.{u}) (k : ℕ) (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C) _⦋k⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinAssociatorSimplexEquiv A B C k t) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A B C (k + 1) t := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (k + 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (k + 1)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A B C (k + 1) t)) = _
    exact Equiv.apply_symm_apply _ _
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A' B' C' (n + 1)).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A' B' C' (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinAssociatorSimplexEquiv A' B' C' n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) h).app _ s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A' B' C' (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g h)) (n + 1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinAssociatorSimplexEquiv A B C n s))
  rw [he, rightJoinTripleEncoding_hom, he]
  exact leftJoinTripleEncoding_hom f g h (n + 1) s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

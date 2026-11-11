module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：三因子の join の両括弧付けの単体を、三つの区間の長さと単体で同定する。
方針：頂点数零を含む join を長さの和で表示し、依存和の括弧を外す。
規約：この段階は次数ごとの全単射であり、単体集合の同型はまだ主張しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の反復 slice と錐の切断の比較の準備。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：join の補った単体を左右の頂点数の和で表す型。
方針：長さと各区間の単体の族に、全頂点数を固定する条件を添える。
規約：n は次数でなく頂点数。空区間も許す。
使われ方：Kerodon §4.3.5（Tag 017V） の反復 join の cast の整理。 -/
abbrev joinSumSimplex (A B : SSet.{u}) (n : ℕ) : Type u :=
  {s : Σ a : ℕ, Σ b : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b // s.1 + s.2.1 = n}

/-- 概要：全頂点数零の join の和表示は高々一点。
方針：和が零なら両区間が空であり、それぞれの補った単体は唯一である。
規約：任意の A・B について成立する。
使われ方：Kerodon §4.3.5（Tag 017V） の空区間への単体作用の自然性。 -/
instance joinSumSimplex_zero_subsingleton (A B : SSet.{u}) :
    Subsingleton (joinSumSimplex A B 0) where
  allEq := by
    rintro ⟨⟨a, b, x, y⟩, h⟩ ⟨⟨c, d, z, w⟩, k⟩
    change a + b = 0 at h
    change c + d = 0 at k
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    have hd : d = 0 := by omega
    subst a b c d
    cases x
    cases y
    cases z
    cases w
    rfl

/-- 概要：join の補った単体は区間の頂点数の和による表示と全単射。
方針：切断を左の長さ、残りを右の長さに取り、和の等式で戻す。
規約：頂点数零では補った唯一の単体に対応する。
使われ方：HTT §1.2.8 の join の結合の全次数の構成。 -/
def augmentedJoinSumEquiv (A B : SSet.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) n ≃ joinSumSimplex A B n := by
  cases n with
  | zero =>
    exact
      { toFun := fun _ ↦ ⟨⟨0, 0, PUnit.unit, PUnit.unit⟩, rfl⟩
        invFun := fun _ ↦ PUnit.unit
        left_inv := fun _ ↦ @Subsingleton.elim PUnit inferInstance _ _
        right_inv := by
          rintro ⟨⟨a, b, x, y⟩, h⟩
          change a + b = 0 at h
          have ha : a = 0 := by omega
          have hb : b = 0 := by omega
          subst a b
          cases x
          cases y
          rfl }
  | succ n =>
    exact
      { toFun := fun s ↦ ⟨⟨s.1.val, n + 1 - s.1.val, s.2.1, s.2.2⟩,
          by
            change s.1.val + (n + 1 - s.1.val) = n + 1
            have h : s.1.val < n + 2 := s.1.isLt
            omega⟩
        invFun := fun ⟨⟨a, b, x, y⟩, h⟩ ↦
          ⟨⟨a, by change a + b = n + 1 at h; change a < n + 2; omega⟩, x,
            cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B) (by change a + b = n + 1 at h; omega : b = n + 1 - a)) y⟩
        left_inv := by
          rintro ⟨a, x, y⟩
          rfl
        right_inv := by
          rintro ⟨⟨a, b, x, y⟩, h⟩
          change a + b = n + 1 at h
          have hb : b = n + 1 - a := by omega
          subst b
          rfl }

/-- 概要：三因子の join の単体を三つの区間の長さと単体で表す型。
方針：三つの頂点数と各因子の単体に、和を固定する条件を添える。
規約：和は (a+b)+c の括弧付け。空区間を排除しない。
使われ方：Kerodon §4.3.5（Tag 017V） の join の二つの括弧付けの共通表示。 -/
abbrev joinTripleSimplex (A B C : SSet.{u}) (n : ℕ) : Type u :=
  {s : Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c // s.1 + s.2.1 + s.2.2.1 = n}

/-- 概要：左括弧の join の和表示を三つの区間の共通表示へ展開する。
方針：左因子の join を和表示に移し、二つの和の等式をまとめる。
規約：補った空単体のケースも同じ写像で扱う。
使われ方：HTT §1.2.8 の (A⋆B)⋆C の再結合の順方向。 -/
def leftJoinSumTripleEquiv (A B C : SSet.{u}) (n : ℕ) :
    joinSumSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C n ≃ joinTripleSimplex A B C n where
  toFun
    | ⟨⟨r, c, t, z⟩, hr⟩ =>
      match augmentedJoinSumEquiv A B r t with
      | ⟨⟨a, b, x, y⟩, hab⟩ => ⟨⟨a, b, c, x, y, z⟩, by
        change r + c = n at hr
        change a + b = r at hab
        change a + b + c = n
        omega⟩
  invFun
    | ⟨⟨a, b, c, x, y, z⟩, h⟩ =>
      ⟨⟨a + b, c, (augmentedJoinSumEquiv A B (a + b)).symm
        ⟨⟨a, b, x, y⟩, rfl⟩, z⟩, h⟩
  left_inv := by
    rintro ⟨⟨r, c, t, z⟩, h⟩
    rcases ht : augmentedJoinSumEquiv A B r t with ⟨⟨a, b, x, y⟩, hab⟩
    change a + b = r at hab
    have hback : (augmentedJoinSumEquiv A B r).symm ⟨⟨a, b, x, y⟩, hab⟩ = t := by
      rw [← ht, Equiv.symm_apply_apply]
    subst r
    apply Subtype.ext
    let f (q : joinSumSimplex A B (a + b)) :
        Σ r : ℕ, Σ c : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) r × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c :=
      ⟨q.val.1 + q.val.2.1, c,
        (augmentedJoinSumEquiv A B (q.val.1 + q.val.2.1)).symm ⟨q.val, rfl⟩, z⟩
    exact (congrArg f ht).trans (congrArg
      (fun q ↦ (⟨a + b, c, q, z⟩ :
        Σ r : ℕ, Σ c : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) r × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c)) hback)
  right_inv := by
    rintro ⟨⟨a, b, c, x, y, z⟩, h⟩
    apply Subtype.ext
    exact congrArg (fun q : joinSumSimplex A B (a + b) ↦
      (⟨q.val.1, q.val.2.1, c, q.val.2.2.1, q.val.2.2.2, z⟩ :
        Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c))
      ((augmentedJoinSumEquiv A B (a + b)).apply_symm_apply ⟨⟨a, b, x, y⟩, rfl⟩)

/-- 概要：右括弧の join の和表示を三つの区間の共通表示へ展開する。
方針：右因子の join を和表示に移し、和の結合律で全頂点数を合わせる。
規約：共通表示では (a+b)+c を用い、単体には変更を加えない。
使われ方：HTT §1.2.8 の A⋆(B⋆C) の再結合の逆方向。 -/
def rightJoinSumTripleEquiv (A B C : SSet.{u}) (n : ℕ) :
    joinSumSimplex A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) n ≃ joinTripleSimplex A B C n where
  toFun
    | ⟨⟨a, r, x, t⟩, hr⟩ =>
      match augmentedJoinSumEquiv B C r t with
      | ⟨⟨b, c, y, z⟩, hbc⟩ => ⟨⟨a, b, c, x, y, z⟩, by
        change a + r = n at hr
        change b + c = r at hbc
        change a + b + c = n
        omega⟩
  invFun
    | ⟨⟨a, b, c, x, y, z⟩, h⟩ =>
      ⟨⟨a, b + c, x, (augmentedJoinSumEquiv B C (b + c)).symm
        ⟨⟨b, c, y, z⟩, rfl⟩⟩, by
          change a + b + c = n at h
          change a + (b + c) = n
          omega⟩
  left_inv := by
    rintro ⟨⟨a, r, x, t⟩, h⟩
    rcases ht : augmentedJoinSumEquiv B C r t with ⟨⟨b, c, y, z⟩, hbc⟩
    change b + c = r at hbc
    have hback : (augmentedJoinSumEquiv B C r).symm ⟨⟨b, c, y, z⟩, hbc⟩ = t := by
      rw [← ht, Equiv.symm_apply_apply]
    subst r
    apply Subtype.ext
    let f (q : joinSumSimplex B C (b + c)) :
        Σ a : ℕ, Σ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) r :=
      ⟨a, q.val.1 + q.val.2.1, x,
        (augmentedJoinSumEquiv B C (q.val.1 + q.val.2.1)).symm ⟨q.val, rfl⟩⟩
    exact (congrArg f ht).trans (congrArg
      (fun q ↦ (⟨a, b + c, x, q⟩ :
        Σ a : ℕ, Σ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) r)) hback)
  right_inv := by
    rintro ⟨⟨a, b, c, x, y, z⟩, h⟩
    apply Subtype.ext
    exact congrArg (fun q : joinSumSimplex B C (b + c) ↦
      (⟨a, q.val.1, q.val.2.1, x, q.val.2.2.1, q.val.2.2.2⟩ :
        Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c))
      ((augmentedJoinSumEquiv B C (b + c)).apply_symm_apply ⟨⟨b, c, y, z⟩, rfl⟩)

/-- 概要：三因子の join の二つの括弧付けは各次数の単体として全単射。
方針：両方を三つの区間の長さと単体の共通表示に移す。
規約：左括弧から右括弧への向き。単体作用との可換性は別に検証する。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の反復 slice の比較に必要な join 結合の準備。 -/
def joinAssociatorSimplexEquiv (A B C : SSet.{u}) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C) _⦋n⦌ ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C)) _⦋n⦌ :=
  (augmentedJoinSumEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C (n + 1)).trans
    ((leftJoinSumTripleEquiv A B C (n + 1)).trans
      (((rightJoinSumTripleEquiv A B C (n + 1)).symm).trans
        (augmentedJoinSumEquiv A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) (n + 1)).symm))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

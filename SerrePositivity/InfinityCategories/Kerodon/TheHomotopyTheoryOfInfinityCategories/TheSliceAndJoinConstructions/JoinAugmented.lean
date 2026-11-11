module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-! # 空次数を含む join の切断表示

概要：補った join の単体も、左右の頂点数による一つの表示で扱う。
方針：頂点数零の唯一の切断を補い、既存の非空次数の表示と同一視する。
規約：既存の join の定義を変更しない。
使われ方：S4 の二重 coslice に必要な join の結合の計算。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：頂点数 r の補った join の切断表示。
方針：左の頂点数を零から r まで走らせる。
規約：r=0 でも型を空にしない。使われ方：三因子の join の統一した表示。 -/
abbrev StableAugJoin (K L : SSet.{u}) (r : ℕ) : Type u :=
  Σ a : Fin (r + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K a.val × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L (r - a.val)

/-- 概要：空次数の切断表示は一点。
方針：切断の上界から零と分かり、両因子も空単体になる。
規約：任意の二因子に対する性質。使われ方：補った join の零次数。 -/
instance stableAugJoin_zero_subsingleton (K L : SSet.{u}) :
    Subsingleton (StableAugJoin K L 0) where
  allEq s t := by
    rcases s with ⟨⟨a, ha⟩, x, y⟩
    rcases t with ⟨⟨b, hb⟩, x', y'⟩
    have hza : a = 0 := by omega
    have hzb : b = 0 := by omega
    subst a
    subst b
    have hx : x = x' := @Subsingleton.elim PUnit inferInstance _ _
    have hy : y = y' := @Subsingleton.elim PUnit inferInstance _ _
    subst x'
    subst y'
    rfl

/-- 概要：補った join の単体と統一した切断表示との同値。
方針：非空次数は既存の表示、空次数は一点どうしの同値を使う。
規約：r は頂点数。使われ方：join の結合同型の各次数の構成。 -/
def stableAugJoinEquiv (K L : SSet.{u}) : (r : ℕ) →
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) r ≃ StableAugJoin K L r
  | 0 =>
    { toFun := fun _ ↦ ⟨0, PUnit.unit, PUnit.unit⟩
      invFun := fun _ ↦ PUnit.unit
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ @Subsingleton.elim (StableAugJoin K L 0) inferInstance _ _ }
  | _ + 1 => Equiv.refl _

/-- 概要：補った切断表示の順序写像による引き戻し。
方針：切断の逆像を取り、左右の制限に沿って各因子を引き戻す。
規約：始域・終域の頂点数は零も許す。
使われ方：結合の組み替えの自然性。 -/
def stableAugJoinMap (K L : SSet.{u}) {r s : ℕ} (α : Fin r →o Fin s)
    (x : StableAugJoin K L s) : StableAugJoin K L r :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α x.1.val, by have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α x.1.val; omega⟩,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α x.1.val) x.2.1,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap L (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α x.1.val) x.2.2⟩

/-- 概要：補った join の切断表示は順序写像の引き戻しと可換。
方針：空の始域は一点性、非空から空の終域は不可能性、他は定義を使う。
規約：任意の二因子と順序写像。
使われ方：二重 coslice の単体作用の検証。 -/
lemma stableAugJoinEquiv_naturality (K L : SSet.{u}) {r s : ℕ}
    (α : Fin r →o Fin s) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) s) :
    stableAugJoinEquiv K L r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) α x) =
      stableAugJoinMap K L α (stableAugJoinEquiv K L s x) := by
  cases r with
  | zero => exact @Subsingleton.elim (StableAugJoin K L 0) inferInstance _ _
  | succ r =>
    cases s with
    | zero => exact Fin.elim0 (α 0)
    | succ s => rfl

/-- 概要：同じ切断を持つ二つの補った join 表示は因子の移送で比較できる。
方針：切断の等式を置換し、直積の外延性を使う。
規約：空次数を含む。使われ方：結合の組み替えの等式の検査。 -/
lemma stableAugJoin_ext {K L : SSet.{u}} {r : ℕ} (s t : StableAugJoin K L r)
    (hc : s.1 = t.1)
    (hl : cast (congrArg (fun a : Fin (r + 1) ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K a.val) hc) s.2.1 = t.2.1)
    (hr : cast (congrArg (fun a : Fin (r + 1) ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L (r - a.val)) hc) s.2.2 = t.2.2) :
    s = t := by
  rcases s with ⟨a, x, y⟩
  rcases t with ⟨b, x', y'⟩
  dsimp only at hc
  subst b
  dsimp only [cast_eq] at hl hr
  subst x'
  subst y'
  rfl


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

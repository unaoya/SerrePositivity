module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：coslice の普遍性の直接構成。
方針：左右の頂点数の和による join の単体表示で、右因子の錐を直接評価する。
規約：join と slice の定義は既存のまま。余極限の一般論は用いない。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の双対の普遍性。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：左右の頂点数を指定した単体で、coslice に付いた錐を評価する。
方針：右区間が空なら p、非空なら右単体 a に付いた錐を `(k,id)` で評価する。
規約：n は全体の次数、l と r は左右の頂点数。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の直接構成。 -/
def sliceUnderEval {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n l : ℕ) :
    (r : ℕ) → (h : l + r = n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r → X _⦋n⦌
  | 0, h, k, _ => p.app _ (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K) (by omega : l = n + 1)) k)
  | r + 1, h, k, a => (f.app (Opposite.op ⦋r⦌) a).val.app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)))

/-- 概要：直接評価は右側の頂点数の等式による移送と整合する。
方針：頂点数を等式で置換する。
規約：和の等式の証明には依存しない。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の既存の切断表示への移送。 -/
lemma sliceUnderEval_castRight {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)
    {n l r r' : ℕ} (he : r = r') (h : l + r = n + 1) (h' : l + r' = n + 1)
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) :
    sliceUnderEval f n l r h k a =
      sliceUnderEval f n l r' h' k (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A) he) a) := by
  subst r'
  rfl

/-- 概要：coslice への射から、join の各次数の単体を直接 X に送る写像。
方針：切断の残りを右側の頂点数として直接評価を適用する。
規約：単体作用との可換性は別に示す。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の逆写像。 -/
def sliceUnderUncurryApp {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex K A n) : X _⦋n⦌ :=
  sliceUnderEval f n s.1.val (n + 1 - s.1.val) (by have := s.1.isLt; omega) s.2.1 s.2.2

/-- 概要：和の表示から構成した単体の直接評価は、指定した左右の頂点数で計算できる。
方針：右側の頂点数の等式による移送の整合性を使う。
規約：空区間も許す。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の自然性。 -/
lemma sliceUnderUncurryApp_mkOfSum {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) {n l r : ℕ} (h : l + r = n + 1)
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) :
    sliceUnderUncurryApp f n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h k a) = sliceUnderEval f n l r h k a :=
  (sliceUnderEval_castRight f (by omega : r = n + 1 - l) h _ k a).symm

/-- 概要：右の標準単体の恒等単体を持つ生成元の引き戻しの式。
方針：和の表示での単体作用と joinMap の作用を計算する。
規約：右因子が非空な場合の式。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の coslice の直接評価の自然性。 -/
lemma sliceUnderGenerator_map_succ (K : SSet.{u}) {m n l r c d : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hn : l + (r + 1) = n + 1)
    (hm : c + (d + 1) = m + 1) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α l = c) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap K Δ[r] α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum hn k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.mkHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapOfSum α hn hm hc)))).app (Opposite.op ⦋m⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum hm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α l c hc) k)
          (stdSimplex.objEquiv.symm (𝟙 ⦋d⦌))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_mkOfSum K Δ[r] α hn hm hc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mkOfSum, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
  rfl

/-- 概要：coslice に付いた錐の直接評価は単体作用と可換。
方針：右区間が空なら p の自然性を使い、非空なら各錐と f の自然性を使う。
規約：左右の頂点数と切断の等式を明示する。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の coslice の普遍性。 -/
lemma sliceUnderEval_naturality {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)
    {m n l r c d : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hn : l + r = n + 1) (hm : c + d = m + 1) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α l = c)
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) :
    sliceUnderEval f m c d hm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α l c hc) k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapOfSum α hn hm hc) a) =
      X.map (SimplexCategory.mkHom α).op (sliceUnderEval f n l r hn k a) := by
  cases r with
  | zero =>
    have hl : l = n + 1 := by omega
    subst hl
    have hcp : c = m + 1 := hc.symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_all α)
    subst hcp
    have hd : d = 0 := by omega
    subst hd
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α (n + 1) (m + 1) hc = α := by ext i; rfl
    change p.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α (n + 1) (m + 1) hc) k) =
      X.map (SimplexCategory.mkHom α).op (p.app _ k)
    rw [hb]
    exact ConcreteCategory.congr_hom (p.naturality (SimplexCategory.mkHom α).op) k
  | succ r =>
    let σ := f.app (Opposite.op ⦋r⦌) a
    have hσ := ConcreteCategory.congr_hom (σ.val.naturality (SimplexCategory.mkHom α).op)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum hn k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)))
    change σ.val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap K Δ[r] α
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum hn k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)))) =
      X.map (SimplexCategory.mkHom α).op (sliceUnderEval f n l (r + 1) hn k a) at hσ
    cases d with
    | zero =>
      have hcp : c = m + 1 := by omega
      subst hcp
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_mkOfSum K Δ[r] α hn hm hc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_zero_right] at hσ
      have hp := ConcreteCategory.congr_hom
        (congrArg (fun g : K ⟶ X ↦ g.app (Opposite.op ⦋m⦌)) σ.property)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α l (m + 1) hc) k)
      change p.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α l (m + 1) hc) k) = _
      exact hp.symm.trans hσ
    | succ d =>
      let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapOfSum α hn hm hc
      have hf := congrArg Subtype.val
        (ConcreteCategory.congr_hom (f.naturality (SimplexCategory.mkHom β).op) a)
      change (f.app _ (A.map (SimplexCategory.mkHom β).op a)).val =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.mkHom β)) ≫ σ.val at hf
      change (f.app _ (A.map (SimplexCategory.mkHom β).op a)).val.app (Opposite.op ⦋m⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum hm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α l c hc) k)
            (stdSimplex.objEquiv.symm (𝟙 ⦋d⦌))) = _
      rw [hf]
      rw [sliceUnderGenerator_map_succ K α hn hm hc] at hσ
      exact hσ

/-- 概要：coslice の直接評価は元の切断表示でも単体作用と可換。
方針：左右の頂点数による表示に直して評価の自然性を適用する。
規約：任意の join の単体を扱う。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の束ねる射の構成。 -/
lemma sliceUnderUncurryApp_naturality {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex K A n) :
    sliceUnderUncurryApp f m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap K A α s) =
      X.map (SimplexCategory.mkHom α).op (sliceUnderUncurryApp f n s) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_eta s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_mkOfSum K A α _
    (Nat.add_sub_of_le (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α s.1.val)) rfl,
    sliceUnderUncurryApp_mkOfSum, sliceUnderUncurryApp_mkOfSum]
  exact sliceUnderEval_naturality f α _ _ rfl _ _

/-- 概要：coslice への射を各単体の錐の直接評価によって join からの射に束ねる。
方針：各次数の評価とその自然性を使う。
規約：任意の単体集合 A、余極限の一般論は使わない。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の coslice の普遍性。 -/
def sliceUnderUncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X where
  app n := ↾sliceUnderUncurryApp f n.unop.len
  naturality _ _ α := ConcreteCategory.hom_ext _ _ (fun s ↦
    sliceUnderUncurryApp_naturality f α.unop.toOrderHom s)

/-- 概要：coslice の直接評価は左包含上で p に一致する。
方針：右区間の空の表示を用いて直接評価を計算する。
規約：任意の coslice への射を扱う。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の固定条件。 -/
lemma sliceUnderUncurryApp_inl {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n : ℕ) (k : K _⦋n⦌) :
    sliceUnderUncurryApp f n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A).app _ k) = p.app _ k := by
  change sliceUnderUncurryApp f n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl k) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_zero_right (L := A) rfl k PUnit.unit, sliceUnderUncurryApp_mkOfSum]
  rfl

/-- 概要：coslice から束ねた射は K 上で p に一致する。
方針：左包含上での直接評価を各次数で適用する。
規約：任意の単体集合 A。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の固定条件。 -/
lemma sliceUnderUncurry_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ sliceUnderUncurry f = p := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  exact sliceUnderUncurryApp_inl f n.unop.len k

/-- 概要：join からの射を各単体に制限して評価すると、元の射の単体上の値に戻る。
方針：右区間が空なら固定条件、非空なら Yoneda 射の恒等単体での値を使う。
規約：左右の頂点数を明示した表示で検証する。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の逆関係。 -/
lemma sliceUnderEval_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) {n l r : ℕ}
    (h : l + r = n + 1) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) :
    sliceUnderEval (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hF) n l r h k a = F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h k a) := by
  cases r with
  | zero =>
    have hl : l = n + 1 := by omega
    subst hl
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_zero_right]
    exact (ConcreteCategory.congr_hom
      (congrArg (fun g : K ⟶ X ↦ g.app (Opposite.op ⦋n⦌)) hF) k).symm
  | succ r =>
    change F.app (Opposite.op ⦋n⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm a)).app _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mkOfSum, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
    have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (SSet.yonedaEquiv.symm a) (r + 1)
        (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)) = a := SSet.yonedaEquiv_symm_app_id a
    rw [ha]

/-- 概要：束ねた射を各単体の Yoneda 射に沿って制限すると、その単体の錐を回収する。
方針：空の右区間では固定条件、非空の右区間では f の自然性を使う。
規約：和の表示での任意の join の単体。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の逆関係。 -/
lemma sliceUnderEval_yoneda {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) {n d l r : ℕ} (a : A _⦋n⦌) (h : l + r = d + 1)
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[n] : SSet.{u}) r) :
    sliceUnderEval f d l r h k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (SSet.yonedaEquiv.symm a) r b) =
      (f.app _ a).val.app (Opposite.op ⦋d⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h k b) := by
  cases r with
  | zero =>
    have hl : l = d + 1 := by omega
    subst hl
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_zero_right]
    exact (ConcreteCategory.congr_hom
      (congrArg (fun g : K ⟶ X ↦ g.app (Opposite.op ⦋d⦌)) (f.app _ a).property) k).symm
  | succ r =>
    let β := stdSimplex.objEquiv b
    have hf := congrArg Subtype.val (ConcreteCategory.congr_hom (f.naturality β.op) a)
    change (f.app _ (A.map β.op a)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map β) ≫ (f.app _ a).val at hf
    change (f.app _ (A.map β.op a)).val.app (Opposite.op ⦋d⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌))) = _
    rw [hf]
    change (f.app _ a).val.app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map β)).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mkOfSum, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (stdSimplex.map β) (r + 1)
        (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)) = b := by
      change stdSimplex.objEquiv.symm ((𝟙 ⦋r⦌) ≫ β) = b
      rw [Category.id_comp]
      exact stdSimplex.objEquiv.symm_apply_apply b
    rw [hb]

/-- 概要：coslice の普遍性。A から coslice への射は K 上 p に一致する join からの射と同値。
方針：各単体に付いた錐を直接評価して束ね、逆は Yoneda 射による制限とする。
規約：任意の単体集合 A。余極限の一般論と quasicategory 性を使わない。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の双対のホーン持ち上げ問題。 -/
@[kerodon 0189]
def sliceUnderEquiv {A K X : SSet.{u}} (p : K ⟶ X) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) ≃ {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p} where
  toFun f := ⟨sliceUnderUncurry f, sliceUnderUncurry_fixed f⟩
  invFun F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F.val F.property
  left_inv f := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    change sliceUnderUncurryApp f d.unop.len
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm a)).app d s) = (f.app n a).val.app d s
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_eta s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mkOfSum, sliceUnderUncurryApp_mkOfSum, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
    exact sliceUnderEval_yoneda f a _ _ _
  right_inv F := by
    apply Subtype.ext
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change sliceUnderUncurryApp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F.val F.property) n.unop.len s = F.val.app n s
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_eta s, sliceUnderUncurryApp_mkOfSum]
    exact sliceUnderEval_curry F.val F.property _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

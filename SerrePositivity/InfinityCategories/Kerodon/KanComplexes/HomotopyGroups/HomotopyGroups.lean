module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Quot

/-!
概要：Kan 複体の正次数のホモトピー類と、その積のための商。
方針：Mathlib の境界定数単体と MulStruct の充填を延長する。
規約：`KanHomotopyGroup X n x` の次数は n + 1。積には最後の面を使う。
使われ方：Kerodon §§3.2.2（Tag 00VJ）–3.2.3（Tag 00W3）、Goerss–Jardine I §7。L9a の基礎。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.KanHomotopyGroup
end SerrePositivity.KST.Spectra.KanHomotopyGroup
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

/-- 概要：正次数の境界定数単体のホモトピー関係。
方針：単位元を第一因子とする積の充填で表す。
規約：次数は n + 1、積の添字は Fin.last n。
使われ方：Kerodon §3.2.3（Tag 00W3）。商と積の代表独立性。 -/
def simplexRel (f g : X.PtSimplex (n + 1) x) : Prop :=
  Nonempty (PtSimplex.MulStruct .const f g (Fin.last n))

/-- 概要：充填による関係は同値関係。
方針：Mathlib の退化単体、対称化、充填の結合則を使う。
規約：X の Kan 性だけを要求する。
使われ方：Kerodon §3.2.3（Tag 00W3）。正次数のホモトピー群の商。 -/
def simplexSetoid (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) :
    Setoid (X.PtSimplex (n + 1) x) where
  r := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel
  iseqv := ⟨fun f ↦ ⟨.oneMul f _⟩,
    fun ⟨h⟩ ↦ ⟨h.oneMulEqSymm⟩,
    fun ⟨h⟩ ⟨h'⟩ ↦ ⟨h.oneMulEqTrans h'⟩⟩

/-- 概要：隣接する二面の RelStruct は互いに移せる。
方針：単位元を左右に置く積の比較と対称化を使う。
規約：正次数の単体に対し、隣接する面 i.castSucc と i.succ を扱う。
使われ方：Kerodon §3.2.3（Tag 00W3）。ホモトピー関係の面添字独立性。 -/
noncomputable def shiftRelStruct [KanComplex X]
    {f g : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (r : PtSimplex.RelStruct f g i.castSucc) : PtSimplex.RelStruct f g i.succ :=
  PtSimplex.relStructSuccEquivMulStruct.symm
    (PtSimplex.relStructCastSuccEquivMulStruct r).mulOneEqOfOneMulEq.mulOneEqSymm

/-- 概要：隣接する二面の RelStruct を逆方向に移す。
方針：右単位による積を対称化し、左単位による積へ変換する。
規約：正次数の単体と隣接する二面。
使われ方：Kerodon §3.2.3（Tag 00W3）。面添字独立性の逆向き。 -/
noncomputable def unshiftRelStruct [KanComplex X]
    {f g : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (r : PtSimplex.RelStruct f g i.succ) : PtSimplex.RelStruct f g i.castSucc :=
  PtSimplex.relStructCastSuccEquivMulStruct.symm
    (PtSimplex.relStructSuccEquivMulStruct r).mulOneEqSymm.oneMulEqOfMulOneEq

/-- 概要：RelStruct の充填の存在は面添字に依存しない。
方針：添字に沿った帰納法で隣接面の比較を繰り返す。
規約：正次数でのみ主張する。
使われ方：Kerodon §3.2.3（Tag 00W3）。Mathlib の任意の RelStruct から商への写像。 -/
theorem nonempty_relStruct_iff_zero [KanComplex X]
    {f g : X.PtSimplex (n + 1) x} (i : Fin (n + 2)) :
    Nonempty (PtSimplex.RelStruct f g i) ↔ Nonempty (PtSimplex.RelStruct f g 0) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    exact (show Nonempty (PtSimplex.RelStruct f g i.succ) ↔
      Nonempty (PtSimplex.RelStruct f g i.castSucc) from
        ⟨fun ⟨r⟩ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.unshiftRelStruct r⟩, fun ⟨r⟩ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.shiftRelStruct r⟩⟩).trans ih

/-- 概要：商に用いる関係は任意の面添字の RelStruct と同値。
方針：最後から二番目の面では定義上の単位積となり、面添字を移す。
規約：正次数 n + 1。
使われ方：Kerodon §§3.2.2（Tag 00VJ）–3.2.3（Tag 00W3）。標準的なホモトピー関係との比較。 -/
theorem simplexRel_iff_relStruct [KanComplex X] {f g : X.PtSimplex (n + 1) x}
    (i : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel f g ↔ Nonempty (PtSimplex.RelStruct f g i) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel f g ↔
      Nonempty (PtSimplex.RelStruct f g (Fin.last n).castSucc) :=
    ⟨fun ⟨r⟩ ↦ ⟨PtSimplex.relStructCastSuccEquivMulStruct.symm r⟩,
      fun ⟨r⟩ ↦ ⟨PtSimplex.relStructCastSuccEquivMulStruct r⟩⟩
  exact h.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nonempty_relStruct_iff_zero _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nonempty_relStruct_iff_zero i).symm)

/-- 概要：Kan 複体の次数 n + 1 のホモトピー類。
方針：境界が基点に定数の単体を充填関係で割る。
規約：零次数は含めず、本レーン固有の名前を使う。
使われ方：Kerodon §§3.2.2（Tag 00VJ）–3.2.3（Tag 00W3）、Goerss–Jardine I §7。 -/
def KanHomotopyGroup (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) : Type u :=
  Quotient (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexSetoid X n x)

namespace KanHomotopyGroup


variable [KanComplex X]

/-- 概要：代表単体のホモトピー類。
方針：商への標準射を使う。
規約：正の次数 n + 1。
使われ方：Kerodon §3.2.2（Tag 00VJ）。群演算の計算。 -/
def mk (f : X.PtSimplex (n + 1) x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x := Quotient.mk _ f

/-- 概要：ホモトピー類の等式は充填関係と同値。
方針：商の実効性を使う。
規約：充填の証人の存在だけを主張する。
使われ方：Kerodon §3.2.3（Tag 00W3）。代表独立性の検証。 -/
theorem mk_eq_iff (f g : X.PtSimplex (n + 1) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel f g := Quotient.eq

/-- 概要：任意の RelStruct の充填は同じホモトピー類を与える。
方針：面添字に依存しない充填関係を商に送る。
規約：充填の面添字は任意。
使われ方：Kerodon §3.2.3（Tag 00W3）。ホモトピー類の計算。 -/
theorem sound {f g : X.PtSimplex (n + 1) x} {i : Fin (n + 2)}
    (r : PtSimplex.RelStruct f g i) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g :=
  Quotient.sound ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct i).2 ⟨r⟩)

/-- 概要：同じ二因子の積の充填は商上で同じ値を持つ。
方針：単位充填と結合則の逆向きを使う。
規約：代表単体自体の一意性は要求しない。
使われ方：Kerodon §3.2.3（Tag 00W3）。積の選択の消去。 -/
theorem mul_unique {f g a b : X.PtSimplex (n + 1) x}
    (h : PtSimplex.MulStruct f g a (Fin.last n))
    (h' : PtSimplex.MulStruct f g b (Fin.last n)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b :=
  Quotient.sound ⟨PtSimplex.MulStruct.assoc' (.oneMul f _) h h'⟩

/-- 概要：積の左因子を関係で置き換えられる。
方針：三因子の充填を結合し直す。
規約：積の面添字は最後の面。
使われ方：Kerodon §3.2.3（Tag 00W3）。商上の積。 -/
theorem mul_congr_left {f f' g a b : X.PtSimplex (n + 1) x}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel f f')
    (h : PtSimplex.MulStruct f g a (Fin.last n))
    (h' : PtSimplex.MulStruct f' g b (Fin.last n)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b := by
  obtain ⟨r⟩ := r
  exact Quotient.sound ⟨PtSimplex.MulStruct.assoc' r h h'⟩

/-- 概要：積の右因子を関係で置き換えられる。
方針：左右の単位充填の比較と結合則を使う。
規約：Kan 性は Mathlib の充填定理で使用する。
使われ方：Kerodon §3.2.3（Tag 00W3）。商上の積。 -/
theorem mul_congr_right {f g g' a b : X.PtSimplex (n + 1) x}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel g g')
    (h : PtSimplex.MulStruct f g a (Fin.last n))
    (h' : PtSimplex.MulStruct f g' b (Fin.last n)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b := by
  obtain ⟨r⟩ := r
  exact Quotient.sound
    ⟨(PtSimplex.MulStruct.assoc h r.mulOneEqOfOneMulEq h').oneMulEqOfMulOneEq⟩

/-- 概要：二つの代表単体の積の充填を選ぶ。
方針：Kan ホーンの充填の存在から選択する。
規約：この代表の選択は後で商により消去する。
使われ方：Kerodon §3.2.3（Tag 00W3）。群の積の構成。 -/
noncomputable def productSimplex (f g : X.PtSimplex (n + 1) x) :
    X.PtSimplex (n + 1) x := (PtSimplex.MulStruct.nonempty f g (Fin.last n)).choose

/-- 概要：選択した積の代表には充填が存在する。
方針：存在定理の選択仕様を使う。
規約：証人の選択は不要。
使われ方：Kerodon §3.2.3（Tag 00W3）。積の群法則。 -/
theorem productSimplex_spec (f g : X.PtSimplex (n + 1) x) :
    Nonempty (PtSimplex.MulStruct f g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex f g) (Fin.last n)) :=
  (PtSimplex.MulStruct.nonempty f g (Fin.last n)).choose_spec

/-- 概要：定数単体の類を単位元とする。
方針：境界定数の代表を商へ送る。
規約：正次数。
使われ方：Kerodon §3.2.3（Tag 00W3）。群の単位元。 -/
instance instOne : One (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk .const⟩

/-- 概要：ホモトピー類の積。
方針：選んだ充填の代表を、両因子の代表独立性により商へ降ろす。
規約：最後の面を積の面とする。
使われ方：Kerodon §3.2.3（Tag 00W3）。ホモトピー群。 -/
noncomputable instance instMul : Mul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) where
  mul a b := Quotient.liftOn₂ a b (fun f g ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex f g)) (by
    intro f g f' g' hf hg
    obtain ⟨h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f g
    obtain ⟨h'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f' g
    obtain ⟨h''⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f' g'
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_congr_left hf h h').trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_congr_right hg h' h''))

/-- 概要：充填で指定された積は商上の積と一致する。
方針：選択した積の充填と比較する。
規約：因子と積は正次数の境界定数単体。
使われ方：Kerodon §3.2.3（Tag 00W3）。群法則と自然性。 -/
theorem mul_eq {f g a : X.PtSimplex (n + 1) x}
    (h : PtSimplex.MulStruct f g a (Fin.last n)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a := by
  obtain ⟨h'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f g
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_unique h' h

/-- 概要：ホモトピー類の積は単位的かつ結合的。
方針：Mathlib の単位充填と三因子の充填を商へ送る。
規約：充填の選択に依存しない。
使われ方：Kerodon §3.2.3（Tag 00W3）。群構造の前段。 -/
noncomputable instance instMonoid : Monoid (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) where
  one_mul a := by
    induction a using Quotient.inductionOn with | h f => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (.oneMul f _)
  mul_one a := by
    induction a using Quotient.inductionOn with | h f => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (.mulOne f _)
  mul_assoc a b c := by
    induction a using Quotient.inductionOn with | h f => ?_
    induction b using Quotient.inductionOn with | h g => ?_
    induction c using Quotient.inductionOn with | h h => ?_
    obtain ⟨hfg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f g
    obtain ⟨hgh⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec g h
    obtain ⟨hfgh⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex g h)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex f g) * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk h = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex f (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex g h))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (PtSimplex.MulStruct.assoc hfg hgh hfgh)

/-- 概要：各ホモトピー類は左逆元を持つ。
方針：代表の外側ホーンを充填して左逆元を作る。
規約：正次数のみ。
使われ方：Kerodon §3.2.3（Tag 00W3）。群構造の構成。 -/
theorem exists_left_inverse (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) : ∃ b, b * a = 1 := by
  induction a using Quotient.inductionOn with | h f => ?_
  obtain ⟨g, ⟨h⟩⟩ := PtSimplex.MulStruct.exists_left_inverse f (Fin.last n)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq h⟩

/-- 概要：各類の左逆元を選ぶ。
方針：外側ホーンの充填で得た左逆元の存在を用いる。
規約：群法則により選択の結果は一意になる。
使われ方：Kerodon §3.2.3（Tag 00W3）。逆元演算。 -/
noncomputable instance instInv : Inv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :=
  ⟨fun a ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.exists_left_inverse a).choose⟩

/-- 概要：正次数のホモトピー類は群をなす。
方針：結合的な単位付き積と全要素の左逆元から構成する。
規約：可換性はこの段階では主張しない。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU）、§3.2.3（Tag 00W3）。 -/
noncomputable instance instGroup : Group (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) where
  __ := (inferInstance : Monoid (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x))
  inv_mul_cancel a := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.exists_left_inverse a).choose_spec

end KanHomotopyGroup

/-- 概要：基点を保つ射による境界定数単体の後合成。
方針：基点の像と境界上の可換条件を使う。
規約：任意の次数 m を許し、Kan 性を必要としない。
使われ方：Kerodon §3.2.2（Tag 00VJ）。π_n の自然性。 -/
@[simps! map]
def mapSimplex {Y : SSet.{u}} {m : ℕ} {y : Y _⦋0⦌}
    (φ : X ⟶ Y) (hφ : φ.app _ x = y) (s : X.PtSimplex m x) :
    Y.PtSimplex m y where
  map := s.map ≫ φ
  comm := by
    rw [← Category.assoc, s.comm]
    simp [hφ]

/-- 概要：単体の後合成は定数代表を保つ。
方針：定数写像の後合成を計算する。
規約：像の基点は hφ で指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。誘導準同型の単位保存。 -/
@[simp]
theorem mapSimplex_const {Y : SSet.{u}} {m : ℕ} {y : Y _⦋0⦌}
    (φ : X ⟶ Y) (hφ : φ.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (m := m) φ hφ .const = .const := by
  ext : 1
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex, hφ]

/-- 概要：基点を保つ射で RelStruct の充填を後合成する。
方針：各面の等式を後合成し、定数面の像を計算する。
規約：任意の次数と面添字を許す。
使われ方：Kerodon §§3.2.2（Tag 00VJ）–3.2.3（Tag 00W3）。ホモトピー関係の自然性。 -/
def mapRelStruct {Y : SSet.{u}} {m : ℕ} {y : Y _⦋0⦌}
    (φ : X ⟶ Y) (hφ : φ.app _ x = y)
    {f g : X.PtSimplex m x} {i : Fin (m + 1)} (r : PtSimplex.RelStruct f g i) :
    PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ g) i where
  map := r.map ≫ φ
  δ_castSucc_map := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
  δ_succ_map := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
  δ_map_of_lt j hj := by rw [← Category.assoc, r.δ_map_of_lt j hj, const_comp, hφ]
  δ_map_of_gt j hj := by rw [← Category.assoc, r.δ_map_of_gt j hj, const_comp, hφ]

/-- 概要：基点を保つ射で MulStruct の充填を後合成する。
方針：三つの指定された面と定数面の後合成を計算する。
規約：正の次数に限らず、MulStruct が定義される任意の添字。
使われ方：Kerodon §3.2.3（Tag 00W3）。誘導写像の積保存。 -/
def mapMulStruct {Y : SSet.{u}} {m : ℕ} {y : Y _⦋0⦌}
    (φ : X ⟶ Y) (hφ : φ.app _ x = y)
    {f g a : X.PtSimplex m x} {i : Fin m} (r : PtSimplex.MulStruct f g a i) :
    PtSimplex.MulStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ a) i where
  map := r.map ≫ φ
  δ_castSucc_castSucc_map := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
  δ_succ_castSucc_map := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
  δ_succ_succ_map := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
  δ_map_of_lt j hj := by rw [← Category.assoc, r.δ_map_of_lt j hj, const_comp, hφ]
  δ_map_of_gt j hj := by rw [← Category.assoc, r.δ_map_of_gt j hj, const_comp, hφ]

namespace KanHomotopyGroup


variable [KanComplex X] {Y Z : SSet.{u}} [KanComplex Y] [KanComplex Z]
  {y : Y _⦋0⦌} {z : Z _⦋0⦌}

/-- 概要：基点を保つ単体集合の射が誘導する群準同型。
方針：代表と充填を後合成し、積の充填の一意性を使う。
規約：像の基点の等式を明示的に渡す。
使われ方：Kerodon §3.2.2（Tag 00VJ）。π_* 同型の界面。 -/
noncomputable def map (φ : X ⟶ Y) (hφ : φ.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x →* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y n y where
  toFun := Quotient.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ) (by
    rintro f g ⟨r⟩
    exact ⟨by simpa using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct φ hφ r⟩)
  map_one' := by change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ .const) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk .const; rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_const]
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h f => ?_
    induction b using Quotient.inductionOn with | h g => ?_
    obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f g
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct φ hφ r)).symm

/-- 概要：誘導準同型を代表単体上で計算する。
方針：商への写像の定義を展開する。
規約：像の基点は hφ で指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。自然性の計算。 -/
@[simp]
theorem map_mk (φ : X ⟶ Y) (hφ : φ.app _ x = y) (f : X.PtSimplex (n + 1) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) φ hφ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ f) := rfl

/-- 概要：恒等射の誘導準同型は恒等準同型。
方針：商の代表で恒等射の後合成を計算する。
規約：同じ基点と次数。
使われ方：Kerodon §3.2.2（Tag 00VJ）。関手の恒等法則。 -/
@[simp]
theorem map_id : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (𝟙 X) (x := x) rfl = MonoidHom.id _ := by
  ext a
  induction a using Quotient.inductionOn with | h f => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (𝟙 X) rfl f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f
  congr 1

/-- 概要：合成射の誘導準同型は誘導準同型の合成。
方針：代表単体の後合成の結合則を使う。
規約：hcomp は合成射による基点の像を指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。関手の合成法則。 -/
theorem map_comp (φ : X ⟶ Y) (hφ : φ.app _ x = y)
    (ψ : Y ⟶ Z) (hψ : ψ.app _ y = z) (hcomp : (φ ≫ ψ).app _ x = z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (φ ≫ ψ) hcomp = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map ψ hψ).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hφ) := by
  ext a
  induction a using Quotient.inductionOn with | h f => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (φ ≫ ψ) hcomp f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex ψ hψ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ f))
  congr 1

end KanHomotopyGroup

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapMulStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapRelStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapSimplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapSimplex_const := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_const

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapSimplex_map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.nonempty_relStruct_iff_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nonempty_relStruct_iff_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.shiftRelStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.shiftRelStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.shiftRelStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.simplexRel := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.simplexRel_iff_relStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexSetoid (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.simplexSetoid := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexSetoid

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.unshiftRelStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.unshiftRelStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.unshiftRelStruct

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.exists_left_inverse := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.exists_left_inverse

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instGroup := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instInv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instInv := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instInv

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMonoid (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMonoid := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMonoid

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMul (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMul := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMul

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instOne (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instOne := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instOne

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map_comp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map_id := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map_mk := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.mk := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.mk_eq_iff := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.mul_congr_left := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_congr_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.mul_congr_right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_congr_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.mul_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.mul_unique := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_unique

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.productSimplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.productSimplex_spec := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.sound := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapMulStruct._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapMulStruct._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapMulStruct._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapMulStruct._proof_4 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapMulStruct._proof_5 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapRelStruct._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapRelStruct._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapRelStruct._proof_4 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapRelStruct._proof_5 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapSimplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapSimplex.congr_simp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.mapSimplex.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.simplexSetoid._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexSetoid._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexSetoid.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.simplexSetoid.match_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexSetoid.match_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instGroup._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instGroup._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instGroup._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instGroup._proof_4 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instGroup._proof_5 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instGroup._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMonoid._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMonoid._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMonoid._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMonoid._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMonoid._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMonoid._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMonoid._proof_4 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMonoid._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMonoid._proof_5 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMonoid._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.instMul._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.instMul._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map._proof_4 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.productSimplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex._proof_1

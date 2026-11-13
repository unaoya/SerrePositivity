module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.GroupCompletion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# モノイドの bar の Segal 座標

概要：一対象圏の nerve の n 単体を n 個のモノイド元で記述する。
方針：隣接する射を取り出し、逆写像を射列への前置で再帰的に構成する。
規約：Segal 1974 Proposition 1.5 の Segal 写像。厳密な積の同型を証明する。
使われ方：群状モノイドの bar のホモトピーファイバー比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial

/--
概要：一対象圏の対象の等式からの射のラベルは単位である。
方針：等式帰納法で恒等射に帰着する。
規約：Segal 1974 Proposition 1.5 の射列の輸送計算。
使われ方：Segal 座標の逆写像の証明。
-/
@[simp] theorem monoidSingleObj_eqToHom (T : MonCat.{u}) {a b : SingleObj T} (h : a = b) :
    (eqToHom h : a ⟶ b) = (1 : T) := by
  cases h
  rfl

/--
概要：有限個のモノイド元から一対象圏の射列を構成する。
方針：末尾の射列に先頭の元を前置する再帰を使う。
規約：Segal 1974 Proposition 1.5 の Segal 写像の逆。
使われ方：bar の各行の積座標。
-/
@[kerodon 04G0]
def monoidWordSimplex (T : MonCat.{u}) : (n : ℕ) → (Fin n → T) → (nerve (SingleObj T)) _⦋n⦌
  | 0, _ => ComposableArrows.mk₀ (SingleObj.star T)
  | n + 1, f => (monoidWordSimplex T n (fun i => f i.succ)).precomp
      (show SingleObj.star T ⟶ _ from f 0)

/--
概要：bar の単体の隣接する射のラベルを取り出す。
方針：順序圏の隣接する頂点の間の射を評価する。
規約：Segal 1974 Proposition 1.5 の Segal 座標。
使われ方：各行をモノイドの有限積へ送る。
-/
def monoidWordLabels (T : MonCat.{u}) {n : ℕ} (F : (nerve (SingleObj T)) _⦋n⦌) : Fin n → T :=
  fun i => F.map' i.val (i.val + 1) (Nat.le_succ _) (by change i.val + 1 ≤ n; omega)

/--
概要：元の列を射列にしてからラベルを読むと元に戻る。
方針：列の長さと最初の添字で帰納する。
規約：Segal 1974 Proposition 1.5 の厳密な積分解。
使われ方：Segal 座標の全単射。
-/
theorem monoidWordLabels_simplex (T : MonCat.{u}) (n : ℕ) (f : Fin n → T) :
    monoidWordLabels T (monoidWordSimplex T n f) = f := by
  induction n with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change monoidWordLabels T (monoidWordSimplex T n (fun k => f k.succ)) j = f j.succ
      exact congrFun (ih (fun k => f k.succ)) j

/--
概要：射列を隣接ラベルから復元すると元の射列に戻る。
方針：一対象圏の対象の一意性と隣接射による射列の外延性を使う。
規約：Segal 1974 Proposition 1.5。射の順序を保つ。
使われ方：bar の各行の積分解。
-/
theorem monoidWordSimplex_labels (T : MonCat.{u}) {n : ℕ}
    (F : (nerve (SingleObj T)) _⦋n⦌) :
    monoidWordSimplex T n (monoidWordLabels T F) = F := by
  refine ComposableArrows.ext (fun _ => Quiver.SingleObj.ext (α := T)) ?_
  intro i hi
  simp only [monoidSingleObj_eqToHom]
  change monoidWordLabels T (monoidWordSimplex T n (monoidWordLabels T F)) ⟨i, hi⟩ =
    ((1 : T) * monoidWordLabels T F ⟨i, hi⟩) * 1
  rw [monoidWordLabels_simplex, mul_one, one_mul]

/--
概要：モノイドの nerve の n 単体と n 個の元の全単射。
方針：隣接ラベルと再帰的な射列構成を互いの逆にする。
規約：Segal 1974 Proposition 1.5 の厳密な Segal 条件。
使われ方：二重単体的 bar の行と有限積の同型。
-/
def monoidWordEquiv (T : MonCat.{u}) (n : ℕ) :
    (nerve (SingleObj T)) _⦋n⦌ ≃ (Fin n → T) where
  toFun := monoidWordLabels T
  invFun := monoidWordSimplex T n
  left_inv := monoidWordSimplex_labels T
  right_inv := monoidWordLabels_simplex T n
/--
概要：Segal 座標はモノイド準同型と可換である。
方針：各隣接射のラベルに準同型を適用する。
規約：Segal 1974 Proposition 1.5 の積分解の自然性。
使われ方：二重単体的 bar の行の同型。
-/
theorem monoidWordLabels_map {T U : MonCat.{u}} (f : T ⟶ U) {n : ℕ}
    (F : (nerve (SingleObj T)) _⦋n⦌) :
    monoidWordLabels U ((SingleObj.mapHom T U f.hom).mapComposableArrows n |>.obj F) =
      fun i => f.hom (monoidWordLabels T F i) := rfl

/--
概要：単体的モノイドの台単体集合の有限積を関数の型で表す。
方針：各単体次数で Fin r からモノイドへの写像を取り、各座標に単体作用を適用する。
規約：Segal 1974 Proposition 1.5 の M の有限積。
使われ方：bar の Segal 同型の終域。
-/
def monoidTupleSpace (M : SimplicialObject MonCat.{u}) (r : ℕ) : SSet.{u} where
  obj n := Fin r → M.obj n
  map f := TypeCat.ofHom (fun a k => (M.map f).hom (a k))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro a
    funext k
    change (M.map (𝟙 n)).hom (a k) = a k
    rw [M.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    funext k
    change (M.map (f ≫ g)).hom (a k) = (M.map g).hom ((M.map f).hom (a k))
    rw [M.map_comp]
    rfl

/--
概要：二重単体的 bar の各行は M の有限積と同型である。
方針：射列の Segal 座標の全単射を全単体次数で自然に束ねる。
規約：Segal 1974 Proposition 1.5 の Segal 条件を厳密同型で供給する。
使われ方：bar の作用のホモトピーファイバー比較。
-/
def monoidBarRowIso (M : SimplicialObject MonCat.{u}) (r : ℕ) :
    (bisimplicialBar M).flip.obj (op ⦋r⦌) ≅ monoidTupleSpace M r :=
  NatIso.ofComponents (fun n => (monoidWordEquiv (M.obj n) r).toIso) (by
    intro i j f
    apply ConcreteCategory.hom_ext
    intro F
    exact (monoidWordLabels_map (M.map f) F).symm)


end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.2.4" (partial := component) "仮定：通常のモノイド T を定値単体モノイドとする（HA の通常モノイドの場合）。結論：bar が SingleObj T の nerve に同型で、その n 単体と n 個の T の元の列が全単射になる（分類空間の構成と Segal 写像の成分に一致）。任意の単体集合からのモノイド再構成は含まれない。"] _root_.SerrePositivity.KST.Comparison.monoidWordEquiv
attribute [cite HA "4.1.2.6" (partial := special) "仮定：通常モノイド T から作った単一対象圏の神経（Lean は HA の集合の場合のこの模型に限る）。結論：n 単体が 1 単体の n 個の列と同定される（この場合の X([n]) の標準同定に一致）。一般の準圏の積としての比較は含まれない。"] _root_.SerrePositivity.KST.Comparison.monoidWordEquiv
attribute [cite HA "4.2.2.1" (partial := special) "仮定：通常のモノイド T の自分自身への正則作用（Lean は HA の X=T の場合に限る）。結論：作用圏の神経の n 単体を基底の n 単体と T の元の組に、基底の n 単体を n 個の T の元に同定する（n 単体の積座標に一致）。Lean は始点で座標を読み、HA の面・退化写像の式と一般の作用の特徴付けは含まれない。"] _root_.SerrePositivity.KST.Comparison.monoidWordEquiv

module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Order.Interval.Finset.Fin

/-!
概要：単体集合の join の直接構成のための頂点数と切断の計算。
方針：空区間に一点を補い、順序写像の先頭区間の逆像で切断を引き戻す。
規約：頂点数 0 は次数 −1 を表す。Day 畳み込みは使わない。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の join と slice の構成。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Join

/-- 概要：頂点数で添字付けた単体。空区間の単体は一点。
方針：頂点数 0 と後続数に分けて定義する。
規約：`augObj K (r+1)` は K の r 単体。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の join の両因子。 -/
def augObj (K : SSet.{u}) : ℕ → Type u
  | 0 => PUnit
  | r + 1 => K _⦋r⦌

/-- 概要：空区間を許す順序写像に沿って単体を引き戻す。
方針：始域が空なら一点に、両方非空なら K の単体作用で写す。
規約：非空から空への順序写像は存在しない。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の join の単体作用。 -/
def augMap (K : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n) : augObj K n → augObj K m :=
  match m, n, α with
  | 0, _, _ => fun _ ↦ PUnit.unit
  | _ + 1, 0, α => Fin.elim0 (α 0)
  | _ + 1, _ + 1, α => K.map (SimplexCategory.mkHom α).op

/-- 概要：補った空単体を含めて恒等写像による引き戻しは恒等。
方針：頂点数が零か後続数かに分ける。規約：空単体では一点の一意性を使う。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の関手法則。 -/
lemma augMap_id (K : SSet.{u}) (n : ℕ) (x : augObj K n) :
    augMap K (OrderHom.id : Fin n →o Fin n) x = x := by
  cases n with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ n => exact ConcreteCategory.congr_hom (K.map_id _) x

/-- 概要：補った空単体を含めて順序写像の合成に沿う引き戻しは反変的。
方針：空区間の場合を分け、非空区間では K の関手法則を使う。
規約：`α.comp β` は α を後に適用する合成。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の関手法則。 -/
lemma augMap_comp (K : SSet.{u}) {l m n : ℕ}
    (α : Fin m →o Fin n) (β : Fin l →o Fin m) (x : augObj K n) :
    augMap K (α.comp β) x = augMap K β (augMap K α x) := by
  cases l with
  | zero => rfl
  | succ l =>
    cases m with
    | zero => exact Fin.elim0 (β 0)
    | succ m =>
      cases n with
      | zero => exact Fin.elim0 (α 0)
      | succ n =>
        exact ConcreteCategory.congr_hom
          (K.map_comp (SimplexCategory.mkHom α).op (SimplexCategory.mkHom β).op) x

/-- 概要：join の n 単体の型を切断位置ごとの直和として与える。
方針：左側の頂点数を `Fin (n+2)` で走らせ、右側は残りの頂点数とする。
規約：切断 0 と n+1 は、それぞれ右と左だけの単体。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の直接構成の次数ごとの型。 -/
def Simplex (K L : SSet.{u}) (n : ℕ) : Type u :=
  Σ ℓ : Fin (n + 2), augObj K ℓ.val × augObj L (n + 1 - ℓ.val)

/-- 概要：順序写像による先頭区間の逆像の頂点数。
方針：先頭区間に入る頂点の有限集合の濃度を取る。
規約：`ℓ` は終域の左側の頂点数で、空区間も許す。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の join の単体作用。 -/
def pullCut {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) : ℕ :=
  (Finset.univ.filter (fun i ↦ (α i).val < ℓ)).card

/-- 概要：切断の逆像の頂点数は始域の頂点数以下。
方針：有限集合が全体集合の部分集合であることから濃度を比較する。
規約：空の順序集合を含む。使われ方：HTT §1.2.8、Kerodon §4.3.5 の添字の境界。 -/
lemma pullCut_le {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) : pullCut α ℓ ≤ m := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin m)

/-- 概要：先頭区間の逆像は、逆像の頂点数で定まる先頭区間に等しい。
方針：入る頂点より前はすべて入り、入らない頂点以後はすべて入らないことを使う。
規約：順序写像の単調性以外の仮定はない。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の左右の制限写像。 -/
lemma lt_pullCut_iff {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) (i : Fin m) :
    i.val < pullCut α ℓ ↔ (α i).val < ℓ := by
  classical
  constructor
  · intro h
    by_contra hn
    have hs : Finset.univ.filter (fun j ↦ (α j).val < ℓ) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hji
      have hmono := α.monotone (le_of_not_gt hji)
      exact hn (lt_of_le_of_lt hmono hj)
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    exact (not_lt_of_ge hc) h
  · intro h
    have hs : Finset.Iic i ⊆ Finset.univ.filter (fun j ↦ (α j).val < ℓ) := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (α.monotone hj) h
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    exact hc

/-- 概要：切断は、各頂点がその左側にあるかどうかで一意に決まる。
方針：異なる二つの切断の小さい方の位置の頂点を検査する。
規約：頂点数の範囲内の切断のみを扱う。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の切断の恒等則。 -/
lemma cut_ext {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (h : ∀ i : Fin n, i.val < a ↔ i.val < b) : a = b := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hab | hba
  · have hi := h ⟨a, by omega⟩
    simp only at hi
    omega
  · have hi := h ⟨b, by omega⟩
    simp only at hi
    omega

/-- 概要：恒等順序写像は切断を変えない。
方針：頂点での切断の特徴づけと一意性を使う。
規約：切断は頂点数以下。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の join の恒等則。 -/
lemma pullCut_id {n : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    pullCut (OrderHom.id : Fin n →o Fin n) ℓ = ℓ :=
  cut_ext (pullCut_le _ _) hℓ (fun i ↦ lt_pullCut_iff _ _ i)

/-- 概要：切断の引き戻しは順序写像の合成に対して反変的。
方針：逆像の有限集合を、先頭区間の特徴づけによって同一視する。
規約：空区間を含む任意の有限順序集合。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の join の合成則。 -/
lemma pullCut_comp {l m n : ℕ} (α : Fin m →o Fin n) (β : Fin l →o Fin m) (ℓ : ℕ) :
    pullCut (α.comp β) ℓ = pullCut β (pullCut α ℓ) := by
  unfold pullCut
  congr 1
  ext i
  simpa [pullCut] using (lt_pullCut_iff α ℓ (β i)).symm

/-- 概要：順序写像を左側の先頭区間に制限した写像。
方針：逆像の切断の特徴づけから終域が左区間に入ることを示す。
規約：始域・終域とも頂点数零を許す。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の左因子の引き戻し。 -/
def leftMap {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) :
    Fin (pullCut α ℓ) →o Fin ℓ where
  toFun i := ⟨(α ⟨i.val, lt_of_lt_of_le i.isLt (pullCut_le α ℓ)⟩).val,
    (lt_pullCut_iff α ℓ _).mp i.isLt⟩
  monotone' _ _ h := α.monotone h

/-- 概要：順序写像を切断より右側の区間に制限し、原点を移した写像。
方針：先頭区間に入らない頂点の像が終域の右側に入ることを使う。
規約：左右の切断位置を引き、右区間の添字を零から数える。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の右因子の引き戻し。 -/
def rightMap {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) :
    Fin (m - pullCut α ℓ) →o Fin (n - ℓ) where
  toFun i :=
    let j : Fin m := ⟨pullCut α ℓ + i.val, by have := i.isLt; omega⟩
    ⟨(α j).val - ℓ, by
      have hj : ¬ j.val < pullCut α ℓ := by dsimp [j]; omega
      have hα : ¬ (α j).val < ℓ := fun h ↦ hj ((lt_pullCut_iff α ℓ j).mpr h)
      have hn := (α j).isLt
      omega⟩
  monotone' i j h := Nat.sub_le_sub_right (α.monotone (by
    change pullCut α ℓ + i.val ≤ pullCut α ℓ + j.val
    exact Nat.add_le_add_left h _)) ℓ

/-- 概要：join の次数ごとの型上での単体作用。
方針：切断を逆像で引き戻し、左右の区間の制限に沿って両因子を引き戻す。
規約：この定義だけでは単体集合の関手法則の証明を含まない。
使われ方：HTT §1.2.8、Kerodon §4.3.5 の join の直接構成。 -/
def simplexMap (K L : SSet.{u}) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    Simplex K L n → Simplex K L m
  | ⟨ℓ, x, y⟩ =>
    ⟨⟨pullCut α ℓ.val, by have := pullCut_le α ℓ.val; omega⟩,
      augMap K (leftMap α ℓ.val) x, augMap L (rightMap α ℓ.val) y⟩

end SerrePositivity.InfinityCategories.Join

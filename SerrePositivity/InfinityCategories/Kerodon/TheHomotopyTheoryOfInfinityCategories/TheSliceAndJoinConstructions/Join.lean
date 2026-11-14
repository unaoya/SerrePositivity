module


public meta import SerrePositivity.Util.Citation
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合の join の直接構成のための頂点数と切断の計算。
方針：空区間に一点を補い、順序写像の先頭区間の逆像で切断を引き戻す。
規約：頂点数 0 は次数 −1 を表す。Day 畳み込みは使わない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join と slice の構成。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-- 概要：頂点数で添字付けた単体。空区間の単体は一点。
方針：頂点数 0 と後続数に分けて定義する。
規約：`augObj K (r+1)` は K の r 単体。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の両因子。 -/
def augObj (K : SSet.{u}) : ℕ → Type u
  | 0 => PUnit
  | r + 1 => K _⦋r⦌

/-- 概要：空区間を許す順序写像に沿って単体を引き戻す。
方針：始域が空なら一点に、両方非空なら K の単体作用で写す。
規約：非空から空への順序写像は存在しない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の単体作用。 -/
def augMap (K : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n) : augObj K n → augObj K m :=
  match m, n, α with
  | 0, _, _ => fun _ ↦ PUnit.unit
  | _ + 1, 0, α => Fin.elim0 (α 0)
  | _ + 1, _ + 1, α => K.map (SimplexCategory.mkHom α).op

/-- 概要：補った空単体を含めて恒等写像による引き戻しは恒等。
方針：頂点数が零か後続数かに分ける。規約：空単体では一点の一意性を使う。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の関手法則。 -/
lemma augMap_id (K : SSet.{u}) (n : ℕ) (x : augObj K n) :
    augMap K (OrderHom.id : Fin n →o Fin n) x = x := by
  cases n with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ n => exact ConcreteCategory.congr_hom (K.map_id _) x

/-- 概要：補った空単体を含めて順序写像の合成に沿う引き戻しは反変的。
方針：空区間の場合を分け、非空区間では K の関手法則を使う。
規約：`α.comp β` は α を後に適用する合成。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の関手法則。 -/
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

/-- 概要：単体集合の射は空単体を補った各次数にも作用する。
方針：空区間では恒等、非空区間では射の成分を使う。
規約：空単体の唯一の元を保つ。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の射への関手性。 -/
def augHom {K L : SSet.{u}} (f : K ⟶ L) : (n : ℕ) → augObj K n → augObj L n
  | 0 => id
  | _n + 1 => f.app _

/-- 概要：空単体を補った射の作用は順序写像による引き戻しと可換。
方針：空区間を分け、非空区間では自然性を適用する。
規約：任意の単体集合の射を扱う。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の joinMap の自然性。 -/
lemma augHom_naturality {K L : SSet.{u}} (f : K ⟶ L) {m n : ℕ}
    (α : Fin m →o Fin n) (x : augObj K n) :
    augHom f m (augMap K α x) = augMap L α (augHom f n x) := by
  cases m with
  | zero => rfl
  | succ m =>
    cases n with
    | zero => exact Fin.elim0 (α 0)
    | succ n => exact ConcreteCategory.congr_hom (f.naturality (SimplexCategory.mkHom α).op) x

/-- 概要：補った単体への恒等射の作用は恒等。
方針：頂点数で場合分けする。規約：空単体も含む。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の joinMap の恒等則。 -/
lemma augHom_id (K : SSet.{u}) (n : ℕ) (x : augObj K n) : augHom (𝟙 K) n x = x := by
  cases n <;> rfl

/-- 概要：補った単体への射の作用は合成を保つ。
方針：頂点数で場合分けする。規約：合成は Mathlib の順序。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の joinMap の合成則。 -/
lemma augHom_comp {K L M : SSet.{u}} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) (x : augObj K n) :
    augHom (f ≫ g) n x = augHom g n (augHom f n x) := by
  cases n <;> rfl

/-- 概要：単射な単体集合の射は補った単体の型でも単射。
方針：空区間では一点性、非空区間では成分の単射性を使う。
規約：仮定は圏論的な単射 `Mono f`。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の部分複体の join。 -/
lemma augHom_injective {K L : SSet.{u}} (f : K ⟶ L) [Mono f] (n : ℕ) :
    Function.Injective (augHom f n) := by
  cases n with
  | zero => intro x y _; exact @Subsingleton.elim PUnit inferInstance x y
  | succ n => exact (mono_iff_injective (f.app _)).mp inferInstance

/-- 概要：join の n 単体の型を切断位置ごとの直和として与える。
方針：左側の頂点数を `Fin (n+2)` で走らせ、右側は残りの頂点数とする。
規約：切断 0 と n+1 は、それぞれ右と左だけの単体。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の直接構成の次数ごとの型。 -/
def Simplex (K L : SSet.{u}) (n : ℕ) : Type u :=
  Σ ℓ : Fin (n + 2), augObj K ℓ.val × augObj L (n + 1 - ℓ.val)

/-- 概要：補った標準単体は、空区間も許す有限順序集合の順序写像と同値。
方針：非空区間では標準単体の表現可能性、空区間では唯一の空写像を使う。
規約：r は頂点数であり、標準単体の次数ではない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の同型。 -/
def stdAugEquiv (n r : ℕ) : augObj (Δ[n] : SSet.{u}) r ≃ (Fin r →o Fin (n + 1)) :=
  match r with
  | 0 =>
    { toFun := fun _ ↦ ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
      invFun := fun _ ↦ PUnit.unit
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ by ext i; exact Fin.elim0 i }
  | r + 1 =>
    { toFun := fun x ↦ (stdSimplex.objEquiv x).toOrderHom
      invFun := fun f ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom f)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- 概要：有限順序集合の二つの順序写像を、切断で連結する。
方針：左側の値を保ち、右側の値には左終域の頂点数を加える。
規約：空区間を許し、r 頂点の始域を切断 ℓ で二分する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join。 -/
def concat {p q r : ℕ} (ℓ : ℕ) (_hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) : Fin r →o Fin (p + q) where
  toFun i := if h : i.val < ℓ then
      ⟨(f ⟨i.val, h⟩).val, by have := (f ⟨i.val, h⟩).isLt; omega⟩
    else
      ⟨p + (g ⟨i.val - ℓ, by have := i.isLt; omega⟩).val,
        by have := (g ⟨i.val - ℓ, by have := i.isLt; omega⟩).isLt; omega⟩
  monotone' a b hab := by
    dsimp only
    split_ifs with ha hb hb
    · exact f.monotone hab
    · change (f _).val ≤ p + (g _).val
      have := (f ⟨a.val, ha⟩).isLt
      omega
    · have : a.val ≤ b.val := hab
      omega
    · change p + (g _).val ≤ p + (g _).val
      exact Nat.add_le_add_left (g.monotone (Nat.sub_le_sub_right hab ℓ)) p

/-- 概要：連結した順序写像の値が左終域に入るのは、始域が左区間にあるときに限る。
方針：切断の左右で場合分けし、それぞれの値の境界を使う。
規約：終域の切断は左側の頂点数 p。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の逆写像。 -/
lemma concat_lt_iff {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (i : Fin r) :
    (concat ℓ hℓ f g i).val < p ↔ i.val < ℓ := by
  by_cases hi : i.val < ℓ
  · simp only [concat, OrderHom.coe_mk, dite_eq_left hi]
    exact iff_of_true (f ⟨i.val, hi⟩).isLt hi
  · simp only [concat, OrderHom.coe_mk, dite_eq_right hi]
    constructor
    · omega
    · exact fun h ↦ (hi h).elim

/-- 概要：join の単体は切断と、その等式で移送した左右の因子で一意に決まる。
方針：切断の等式で置換し、積と依存和の外延性を適用する。
規約：切断の等式は命題的でよく、両因子の cast を明示する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の関手法則と部分複体。 -/
@[ext (iff := false)]
lemma Simplex.ext {K L : SSet.{u}} {n : ℕ} (s t : Simplex K L n)
    (hcut : s.1 = t.1)
    (hleft : cast (congrArg (fun ℓ : Fin (n + 2) ↦ augObj K ℓ.val) hcut) s.2.1 = t.2.1)
    (hright : cast (congrArg (fun ℓ : Fin (n + 2) ↦ augObj L (n + 1 - ℓ.val)) hcut)
      s.2.2 = t.2.2) : s = t := by
  rcases s with ⟨ℓ, x, y⟩
  rcases t with ⟨ℓ', x', y'⟩
  dsimp only at hcut
  cases hcut
  cases hleft
  cases hright
  rfl

/-- 概要：頂点数を等式で移送しても、同じ順序写像に沿う単体の引き戻しは一致する。
方針：頂点数と単体を置換し、順序写像の外延性を使う。
規約：写像の一致は頂点の自然数値で与え、始域と終域の cast を明示する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の切断の等式に沿う移送。 -/
lemma augMap_congr (K : SSet.{u}) {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (α : Fin m →o Fin n) (β : Fin m' →o Fin n')
    (hα : ∀ (i : Fin m) (j : Fin m'), i.val = j.val → (α i).val = (β j).val)
    (x : augObj K n) (x' : augObj K n')
    (hx : cast (congrArg (augObj K) hn) x = x') :
    cast (congrArg (augObj K) hm) (augMap K α x) = augMap K β x' := by
  subst m' n'
  dsimp only [cast_eq] at hx ⊢
  subst x'
  have h : α = β := by
    ext i
    exact hα i i rfl
  rw [h]

/-- 概要：順序写像による先頭区間の逆像の頂点数。
方針：先頭区間に入る頂点の有限集合の濃度を取る。
規約：`ℓ` は終域の左側の頂点数で、空区間も許す。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の単体作用。 -/
def pullCut {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) : ℕ :=
  (Finset.univ.filter (fun i ↦ (α i).val < ℓ)).card

/-- 概要：切断の逆像の頂点数は始域の頂点数以下。
方針：有限集合が全体集合の部分集合であることから濃度を比較する。
規約：空の順序集合を含む。使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の添字の境界。 -/
lemma pullCut_le {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) : pullCut α ℓ ≤ m := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin m)

/-- 概要：先頭区間の逆像は、逆像の頂点数で定まる先頭区間に等しい。
方針：入る頂点より前はすべて入り、入らない頂点以後はすべて入らないことを使う。
規約：順序写像の単調性以外の仮定はない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の左右の制限写像。 -/
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
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の切断の恒等則。 -/
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
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の恒等則。 -/
lemma pullCut_id {n : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    pullCut (OrderHom.id : Fin n →o Fin n) ℓ = ℓ :=
  cut_ext (pullCut_le _ _) hℓ (fun i ↦ lt_pullCut_iff _ _ i)

/-- 概要：切断の引き戻しは順序写像の合成に対して反変的。
方針：逆像の有限集合を、先頭区間の特徴づけによって同一視する。
規約：空区間を含む任意の有限順序集合。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の合成則。 -/
lemma pullCut_comp {l m n : ℕ} (α : Fin m →o Fin n) (β : Fin l →o Fin m) (ℓ : ℕ) :
    pullCut (α.comp β) ℓ = pullCut β (pullCut α ℓ) := by
  unfold pullCut
  congr 1
  ext i
  simpa [pullCut] using (lt_pullCut_iff α ℓ (β i)).symm

/-- 概要：空の先頭区間の逆像は空。
方針：空の条件でフィルターした有限集合の濃度を計算する。
規約：始域が空でも成り立つ。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の右包含。 -/
lemma pullCut_zero {m n : ℕ} (α : Fin m →o Fin n) : pullCut α 0 = 0 := by
  simp [pullCut]

/-- 概要：終域全体の逆像は始域全体。
方針：すべての頂点が終域の頂点数未満であることを使う。
規約：始域が空でも成り立つ。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の左包含。 -/
lemma pullCut_all {m n : ℕ} (α : Fin m →o Fin n) : pullCut α n = m := by
  simp [pullCut]

/-- 概要：二つの順序写像を連結してから左終域の逆像を取ると元の切断に戻る。
方針：連結した値の左終域への所属で切断を特徴づける。
規約：空の左右区間も含む。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の同型。 -/
lemma pullCut_concat {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) :
    pullCut (concat ℓ hℓ f g) p = ℓ :=
  cut_ext (pullCut_le _ _) hℓ (fun i ↦
    (lt_pullCut_iff _ _ i).trans (concat_lt_iff ℓ hℓ f g i))

/-- 概要：順序写像を左側の先頭区間に制限した写像。
方針：逆像の切断の特徴づけから終域が左区間に入ることを示す。
規約：始域・終域とも頂点数零を許す。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の左因子の引き戻し。 -/
def leftMap {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) :
    Fin (pullCut α ℓ) →o Fin ℓ where
  toFun i := ⟨(α ⟨i.val, lt_of_lt_of_le i.isLt (pullCut_le α ℓ)⟩).val,
    (lt_pullCut_iff α ℓ _).mp i.isLt⟩
  monotone' _ _ h := α.monotone h

/-- 概要：順序写像を切断より右側の区間に制限し、原点を移した写像。
方針：先頭区間に入らない頂点の像が終域の右側に入ることを使う。
規約：左右の切断位置を引き、右区間の添字を零から数える。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の右因子の引き戻し。 -/
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
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の直接構成。 -/
def simplexMap (K L : SSet.{u}) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    Simplex K L n → Simplex K L m
  | ⟨ℓ, x, y⟩ =>
    ⟨⟨pullCut α ℓ.val, by have := pullCut_le α ℓ.val; omega⟩,
      augMap K (leftMap α ℓ.val) x, augMap L (rightMap α ℓ.val) y⟩

/-- 概要：join の次数ごとの単体作用は恒等順序写像を恒等に送る。
方針：切断を `pullCut_id` で移送し、左右の制限が恒等になることを示す。
規約：移送は `Simplex.ext` で明示し、空区間も含める。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の恒等則。 -/
lemma simplexMap_id (K L : SSet.{u}) (n : ℕ) (s : Simplex K L n) :
    simplexMap K L OrderHom.id s = s := by
  rcases s with ⟨ℓ, x, y⟩
  have hc := pullCut_id ℓ.val (Nat.le_of_lt_succ ℓ.isLt)
  apply Simplex.ext _ _ (Fin.ext hc)
  · exact (augMap_congr K hc rfl (leftMap OrderHom.id ℓ.val) OrderHom.id
      (fun i j hij ↦ hij) x x rfl).trans (augMap_id K _ x)
  · exact (augMap_congr L (congrArg (fun c ↦ n + 1 - c) hc) rfl
      (rightMap OrderHom.id ℓ.val) OrderHom.id
      (fun i j hij ↦ by
        change pullCut OrderHom.id ℓ.val + i.val - ℓ.val = j.val
        omega) y y rfl).trans (augMap_id L _ y)

/-- 概要：join の次数ごとの単体作用は順序写像の合成に対して反変的。
方針：切断を `pullCut_comp` で移送し、左右の制限写像の合成を比較する。
規約：右側の添字の原点移動を自然数の等式で確認する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の合成則。 -/
lemma simplexMap_comp (K L : SSet.{u}) {l m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (l + 1) →o Fin (m + 1))
    (s : Simplex K L n) :
    simplexMap K L (α.comp β) s = simplexMap K L β (simplexMap K L α s) := by
  rcases s with ⟨ℓ, x, y⟩
  have hc := pullCut_comp α β ℓ.val
  apply Simplex.ext _ _ (Fin.ext hc)
  · refine (augMap_congr K hc rfl (leftMap (α.comp β) ℓ.val)
      ((leftMap α ℓ.val).comp (leftMap β (pullCut α ℓ.val))) ?_ x x rfl).trans ?_
    · intro i j hij
      change (α (β ⟨i.val, _⟩)).val = (α (β ⟨j.val, _⟩)).val
      exact congrArg (fun z : Fin (l + 1) ↦ (α (β z)).val) (Fin.ext hij)
    · exact augMap_comp K _ _ x
  · refine (augMap_congr L (congrArg (fun c ↦ l + 1 - c) hc) rfl
      (rightMap (α.comp β) ℓ.val)
      ((rightMap α ℓ.val).comp (rightMap β (pullCut α ℓ.val))) ?_ y y rfl).trans ?_
    · intro i j hij
      have hβ : pullCut α ℓ.val ≤
          (β ⟨pullCut β (pullCut α ℓ.val) + j.val, by have := j.isLt; omega⟩).val := by
        apply Nat.le_of_not_lt
        intro h
        have := (lt_pullCut_iff β (pullCut α ℓ.val) _).mpr h
        dsimp only at this
        omega
      change (α (β ⟨pullCut (α.comp β) ℓ.val + i.val, _⟩)).val - ℓ.val =
        (α ⟨pullCut α ℓ.val +
          ((β ⟨pullCut β (pullCut α ℓ.val) + j.val, _⟩).val - pullCut α ℓ.val), _⟩).val - ℓ.val
      apply congrArg (fun z : Fin (m + 1) ↦ (α z).val - ℓ.val)
      apply Fin.ext
      have he : (⟨pullCut (α.comp β) ℓ.val + i.val, by have := i.isLt; omega⟩ : Fin (l + 1)) =
          ⟨pullCut β (pullCut α ℓ.val) + j.val, by have := j.isLt; omega⟩ :=
        Fin.ext (by
          change pullCut (α.comp β) ℓ.val + i.val = pullCut β (pullCut α ℓ.val) + j.val
          omega)
      change (β _).val = pullCut α ℓ.val + ((β _).val - pullCut α ℓ.val)
      rw [he]
      omega
    · exact augMap_comp L _ _ y

/-- 概要：左因子の単体を右区間が空の join の単体にする。
方針：切断を全頂点数に取り、空の右区間に一点を補う。
規約：左単体の次数は変えない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の左包含。 -/
def Simplex.inl {K L : SSet.{u}} {n : ℕ} (x : K _⦋n⦌) : Simplex K L n :=
  ⟨⟨n + 1, by omega⟩, x, by simp only [Nat.sub_self, augObj]; exact PUnit.unit⟩

/-- 概要：右因子の単体を左区間が空の join の単体にする。
方針：切断を零に取り、空の左区間に一点を補う。
規約：右単体の次数は変えない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の右包含。 -/
def Simplex.inr {K L : SSet.{u}} {n : ℕ} (y : L _⦋n⦌) : Simplex K L n :=
  ⟨⟨0, by omega⟩, PUnit.unit, y⟩

/-- 概要：左包含は順序写像による引き戻しと可換。
方針：全区間の逆像を移送し、左の制限が元の写像であることを確認する。
規約：空の右因子は一点の一意性で処理する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の joinInl の自然性。 -/
lemma simplexMap_inl (K L : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (x : K _⦋n⦌) :
    simplexMap K L α (Simplex.inl x) = Simplex.inl (augMap K α x) := by
  have hc := pullCut_all α
  apply Simplex.ext _ _ (Fin.ext hc)
  · exact augMap_congr K hc rfl _ α (fun i j hij ↦ by
      change (α ⟨i.val, _⟩).val = (α j).val
      exact congrArg (fun z ↦ (α z).val) (Fin.ext hij)) x x rfl
  · exact @Subsingleton.elim (augObj L (m + 1 - (m + 1)))
      (by simp only [Nat.sub_self, augObj]; infer_instance) _ _

/-- 概要：右包含は順序写像による引き戻しと可換。
方針：空の先頭区間の逆像を移送し、右の制限が元の写像であることを確認する。
規約：空の左因子は一点の一意性で処理する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の joinInr の自然性。 -/
lemma simplexMap_inr (K L : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (y : L _⦋n⦌) :
    simplexMap K L α (Simplex.inr y) = Simplex.inr (augMap L α y) := by
  have hc := pullCut_zero α
  apply Simplex.ext _ _ (Fin.ext hc)
  · exact @Subsingleton.elim PUnit inferInstance _ _
  · exact augMap_congr L (congrArg (fun c ↦ m + 1 - c) hc) rfl _ α
      (fun i j hij ↦ by
        change (α ⟨pullCut α 0 + i.val, _⟩).val - 0 = (α j).val
        apply congrArg (fun z ↦ (α z).val)
        exact Fin.ext (by change pullCut α 0 + i.val = j.val; omega)) y y rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：二つの単体集合の join を、切断ごとの単体の直和から直接構成する。
方針：順序写像の先頭区間の逆像に沿って両因子を引き戻す。
規約：空区間の因子は一点。Day 畳み込みやモデル構造は用いない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の slice と錐の基礎。 -/
@[kerodon 0177]
def join (K L : SSet.{u}) : SSet.{u} where
  obj n := Join.Simplex K L n.unop.len
  map α := ↾(Join.simplexMap K L α.unop.toOrderHom)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro s
    exact Join.simplexMap_id K L n.unop.len s
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro s
    exact Join.simplexMap_comp K L α.unop.toOrderHom β.unop.toOrderHom s

/-- 概要：二つの単体集合の射が join に誘導する射。
方針：切断を固定し、左右の単体にそれぞれ射を適用する。
規約：空区間の一点は固定する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の slice の単体作用と図式の変更。 -/
def joinMap {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    join K L ⟶ join K' L' where
  app n := ↾fun s ↦ ⟨s.1, Join.augHom f _ s.2.1, Join.augHom g _ s.2.2⟩
  naturality a b α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨ℓ, x, y⟩
    refine Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact Join.augHom_naturality f _ x
    · exact Join.augHom_naturality g _ y

/-- 概要：join に誘導される恒等射は恒等射。
方針：切断を固定したまま両因子の恒等則を使う。
規約：空区間も含める。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の join の関手性。 -/
lemma joinMap_id (K L : SSet.{u}) : joinMap (𝟙 K) (𝟙 L) = 𝟙 (join K L) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨ℓ, x, y⟩
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · exact Join.augHom_id K _ x
  · exact Join.augHom_id L _ y

/-- 概要：join の射への作用は左右の合成を保つ。
方針：切断を固定し、補った単体に対する合成則を使う。
規約：左右それぞれの合成の向きを保つ。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の slice の関手法則。 -/
lemma joinMap_comp {K K' K'' L L' L'' : SSet.{u}}
    (f : K ⟶ K') (f' : K' ⟶ K'') (g : L ⟶ L') (g' : L' ⟶ L'') :
    joinMap (f ≫ f') (g ≫ g') = joinMap f g ≫ joinMap f' g' := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨ℓ, x, y⟩
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · exact Join.augHom_comp f f' _ x
  · exact Join.augHom_comp g g' _ y

/-- 概要：左右の射が単射なら join に誘導される射も単射。
方針：像の切断の一致と、両因子の成分の単射性を使う。
規約：仮定は `Mono f` と `Mono g`。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の部分複体の join の包含。 -/
instance joinMap_mono {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') [Mono f] [Mono g] :
    Mono (joinMap f g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  rintro ⟨ℓ, x, y⟩ ⟨ℓ', x', y'⟩ h
  have hc : ℓ = ℓ' := congrArg Sigma.fst h
  subst ℓ'
  have hp := eq_of_heq (Sigma.mk.inj h).2
  have hl := (Join.augHom_injective f ℓ.val) (congrArg Prod.fst hp)
  have hr := (Join.augHom_injective g (n.unop.len + 1 - ℓ.val)) (congrArg Prod.snd hp)
  exact congrArg (Sigma.mk ℓ) (Prod.ext hl hr)

/-- 概要：join の左因子からの包含。
方針：各単体を右区間が空の単体に送る。
規約：切断はその次数の全頂点数。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の slice の射影。 -/
def joinInl (K L : SSet.{u}) : K ⟶ join K L where
  app _ := ↾Join.Simplex.inl
  naturality _ _ α := ConcreteCategory.hom_ext _ _ (fun x ↦
    (Join.simplexMap_inl K L α.unop.toOrderHom x).symm)

/-- 概要：join の右因子からの包含。
方針：各単体を左区間が空の単体に送る。
規約：切断は零。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の slice の固定条件。 -/
def joinInr (K L : SSet.{u}) : L ⟶ join K L where
  app _ := ↾Join.Simplex.inr
  naturality _ _ α := ConcreteCategory.hom_ext _ _ (fun y ↦
    (Join.simplexMap_inr K L α.unop.toOrderHom y).symm)

/-- 概要：左包含は左右の射に関して自然。
方針：左因子の単体と空の右区間への作用を計算する。
規約：合成は左包含の後に joinMap を適用する順序。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の slice の固定条件。 -/
@[reassoc]
lemma joinInl_joinMap {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    joinInl K L ≫ joinMap f g = f ≫ joinInl K' L' := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · exact @Subsingleton.elim (Join.augObj L' (n.unop.len + 1 - (n.unop.len + 1)))
      (by simp only [Nat.sub_self, Join.augObj]; infer_instance) _ _

/-- 概要：右包含は左右の射に関して自然。
方針：右因子の単体と空の左区間への作用を計算する。
規約：合成は右包含の後に joinMap を適用する順序。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の slice の固定条件。 -/
@[reassoc]
lemma joinInr_joinMap {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    joinInr K L ≫ joinMap f g = g ≫ joinInr K' L' := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro y
  rfl

/-- 概要：左の部分複体と全右因子の join を、全 join の部分複体として実現する。
方針：単射 `joinMap A₀.ι (𝟙 B)` の像を取る。
規約：部分複体の単体集合との同型は `joinSubcomplexLeftIso`。
使われ方：HTT 2.1.2.3、Kerodon §4.3.6（Tag 018E） の pushout-join の始域。 -/
def joinSubcomplexLeft {A : SSet.{u}} (A₀ : A.Subcomplex) (B : SSet.{u}) :
    (join A B).Subcomplex :=
  Subfunctor.range (joinMap A₀.ι (𝟙 B))

/-- 概要：全左因子と右の部分複体の join を、全 join の部分複体として実現する。
方針：単射 `joinMap (𝟙 A) B₀.ι` の像を取る。
規約：部分複体の単体集合との同型は `joinSubcomplexRightIso`。
使われ方：HTT 2.1.2.3、Kerodon §4.3.6（Tag 018E） の pushout-join の始域。 -/
def joinSubcomplexRight (A : SSet.{u}) {B : SSet.{u}} (B₀ : B.Subcomplex) :
    (join A B).Subcomplex :=
  Subfunctor.range (joinMap (𝟙 A) B₀.ι)

/-- 概要：二つの片側の部分複体の join の和。
方針：部分複体の完備束の上限を取る。
規約：始域は `(A₀ ⋆ B) ∪ (A ⋆ B₀)`。
使われ方：HTT 2.1.2.3、Kerodon §4.3.6（Tag 018E） の pushout-join の包含の始域。 -/
@[kerodon 018H]
def joinUnion {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    (join A B).Subcomplex :=
  joinSubcomplexLeft A₀ B ⊔ joinSubcomplexRight A B₀

/-- 概要：左の部分複体の join と、その全 join 内の像は同型。
方針：単射な自然変換から像への射が同型であることを使う。
規約：対象は部分複体の単体集合。
使われ方：HTT 2.1.2.3、Kerodon §4.3.6（Tag 018E） の部分複体による pushout-join。 -/
noncomputable def joinSubcomplexLeftIso {A : SSet.{u}} (A₀ : A.Subcomplex) (B : SSet.{u}) :
    join (A₀ : SSet.{u}) B ≅ (joinSubcomplexLeft A₀ B : SSet.{u}) :=
  by
    letI : Mono (joinMap A₀.ι (𝟙 B)) := joinMap_mono _ _
    letI := Subfunctor.instIsIsoFunctorTypeToRangeOfMono (joinMap A₀.ι (𝟙 B))
    exact asIso (Subfunctor.toRange (joinMap A₀.ι (𝟙 B)))

/-- 概要：右の部分複体の join と、その全 join 内の像は同型。
方針：単射な自然変換から像への射が同型であることを使う。
規約：対象は部分複体の単体集合。
使われ方：HTT 2.1.2.3、Kerodon §4.3.6（Tag 018E） の部分複体による pushout-join。 -/
noncomputable def joinSubcomplexRightIso (A : SSet.{u}) {B : SSet.{u}} (B₀ : B.Subcomplex) :
    join A (B₀ : SSet.{u}) ≅ (joinSubcomplexRight A B₀ : SSet.{u}) :=
  by
    letI : Mono (joinMap (𝟙 A) B₀.ι) := joinMap_mono _ _
    letI := Subfunctor.instIsIsoFunctorTypeToRangeOfMono (joinMap (𝟙 A) B₀.ι)
    exact asIso (Subfunctor.toRange (joinMap (𝟙 A) B₀.ι))

/-- 概要：左の部分複体の像への同型は全 join への包含と整合する。
方針：像への射の定義から計算する。
規約：同型の順方向の射を使う。
使われ方：HTT 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ問題の翻訳。 -/
lemma joinSubcomplexLeftIso_hom_ι {A : SSet.{u}} (A₀ : A.Subcomplex) (B : SSet.{u}) :
    (joinSubcomplexLeftIso A₀ B).hom ≫ (joinSubcomplexLeft A₀ B).ι =
      joinMap A₀.ι (𝟙 B) := rfl

/-- 概要：右の部分複体の像への同型は全 join への包含と整合する。
方針：像への射の定義から計算する。
規約：同型の順方向の射を使う。
使われ方：HTT 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ問題の翻訳。 -/
lemma joinSubcomplexRightIso_hom_ι (A : SSet.{u}) {B : SSet.{u}} (B₀ : B.Subcomplex) :
    (joinSubcomplexRightIso A B₀).hom ≫ (joinSubcomplexRight A B₀).ι =
      joinMap (𝟙 A) B₀.ι := rfl

/-- 概要：空の単体集合と L の join は L と同型。
方針：左区間が非空なら空の部分複体の単体が存在せず、切断零のみが残る。
規約：空の単体集合を任意の A の空部分複体として表す。追加の仮定はない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の空 join の単位則。 -/
noncomputable def emptyJoinIso (A L : SSet.{u}) :
    join ((⊥ : A.Subcomplex) : SSet.{u}) L ≅ L := by
  let E : SSet.{u} := (⊥ : A.Subcomplex)
  haveI : IsIso (joinInr E L) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    rw [isIso_iff_bijective]
    constructor
    · intro x y h
      exact congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h).2)
    · rintro ⟨⟨ℓ, hℓ⟩, x, y⟩
      cases ℓ with
      | zero =>
        exact ⟨y, by cases x; rfl⟩
      | succ ℓ =>
        exact False.elim x.property
  exact (asIso (joinInr E L)).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions



namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-- 概要：逆像の切断を命題的に等しい頂点数 c で表示した左の制限。
方針：先頭区間の逆像の特徴づけに切断の等式を適用する。
規約：切断の移送は hc で明示する。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.3（Tag 016K） の slice の直接評価。 -/
def leftMapAt {m n : ℕ} (α : Fin m →o Fin n) (ℓ c : ℕ) (hc : pullCut α ℓ = c) :
    Fin c →o Fin ℓ where
  toFun i := ⟨(α ⟨i.val, by have := pullCut_le α ℓ; omega⟩).val,
    (lt_pullCut_iff α ℓ _).mp (by change i.val < pullCut α ℓ; have := i.isLt; omega)⟩
  monotone' _ _ h := α.monotone h

/-- 概要：逆像の切断を命題的に等しい頂点数 c で表示した右の制限。
方針：切断 c だけ始域の添字をずらし、終域の切断を値から引く。
規約：空区間も含む。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.3（Tag 016K） の slice の直接評価。 -/
def rightMapAt {m n : ℕ} (α : Fin m →o Fin n) (ℓ c : ℕ) (hc : pullCut α ℓ = c) :
    Fin (m - c) →o Fin (n - ℓ) where
  toFun i :=
    let a : Fin m := ⟨c + i.val, by have := i.isLt; omega⟩
    ⟨(α a).val - ℓ, by
      have hn := (α a).isLt
      have hα : ℓ ≤ (α a).val := by
        apply Nat.le_of_not_lt
        intro h
        have := (lt_pullCut_iff α ℓ a).mpr h
        dsimp [a] at this
        omega
      omega⟩
  monotone' i j h := Nat.sub_le_sub_right (α.monotone (Nat.add_le_add_left h c)) ℓ

/-- 概要：単体作用を指定した逆像の切断 c で計算する。
方針：切断の ext 補題と補った単体の移送補題を適用する。
規約：逆像の頂点数が零か非零かで場合分けするための形。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.3（Tag 016K） の直接評価の自然性。 -/
lemma simplexMap_eq_at (A K : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (ℓ : Fin (n + 2))
    (c : ℕ) (hc : pullCut α ℓ.val = c) (a : augObj A ℓ.val) (k : augObj K (n + 1 - ℓ.val)) :
    simplexMap A K α ⟨ℓ, a, k⟩ =
      ⟨⟨c, by have := pullCut_le α ℓ.val; omega⟩,
        augMap A (leftMapAt α ℓ.val c hc) a, augMap K (rightMapAt α ℓ.val c hc) k⟩ := by
  refine Simplex.ext _ _ (Fin.ext hc) ?_ ?_
  · exact augMap_congr A hc rfl _ _ (fun i j hij ↦ by
      change (α ⟨i.val, _⟩).val = (α ⟨j.val, _⟩).val
      exact congrArg (fun z ↦ (α z).val) (Fin.ext hij)) a a rfl
  · exact augMap_congr K (congrArg (fun d ↦ m + 1 - d) hc) rfl _ _
      (fun i j hij ↦ by
        change (α ⟨pullCut α ℓ.val + i.val, _⟩).val - ℓ.val =
          (α ⟨c + j.val, _⟩).val - ℓ.val
        exact congrArg (fun z ↦ (α z).val - ℓ.val) (Fin.ext (by
          change pullCut α ℓ.val + i.val = c + j.val
          omega))) k k rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-- 概要：補った標準単体の順序写像表示は引き戻しと可換。
方針：空区間を除き、表現可能単体の作用を計算する。
規約：r と s は頂点数。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の自然性。 -/
lemma stdAugEquiv_augMap (n : ℕ) {r s : ℕ} (α : Fin r →o Fin s)
    (x : augObj (Δ[n] : SSet.{u}) s) (i : Fin r) :
    stdAugEquiv n r (augMap Δ[n] α x) i = stdAugEquiv n s x (α i) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
    cases s with
    | zero => exact Fin.elim0 (α i)
    | succ s => rfl

/-- 概要：順序写像の連結の左区間での値。
方針：切断の左側の分岐を計算する。
規約：空区間を含め、頂点 i の左側への所属を明示する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の単射性。 -/
lemma concat_of_lt {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (i : Fin r) (hi : i.val < ℓ) :
    (concat ℓ hℓ f g i).val = (f ⟨i.val, hi⟩).val := by
  simp only [concat, OrderHom.coe_mk, dite_eq_left hi]

/-- 概要：順序写像の連結の右区間での値。
方針：切断の右側の分岐を計算する。
規約：右区間では左終域の頂点数を値に加える。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の全射性。 -/
lemma concat_of_ge {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (i : Fin r) (hi : ℓ ≤ i.val) :
    (concat ℓ hℓ f g i).val = p + (g ⟨i.val - ℓ, by have := i.isLt; omega⟩).val := by
  simp only [concat, OrderHom.coe_mk, dite_eq_right (not_lt.mpr hi)]

/-- 概要：標準単体の join の単体を、両終域を連結した有限順序集合への写像にする。
方針：左右の標準単体を順序写像として読み、切断位置で連結する。
規約：終域の頂点数は `(i+1)+(j+1)` と書く。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の同型。 -/
def stdEncode (i j n : ℕ) (s : Simplex (Δ[i] : SSet.{u}) Δ[j] n) :
    Fin (n + 1) →o Fin ((i + 1) + (j + 1)) :=
  concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (stdAugEquiv i _ s.2.1) (stdAugEquiv j _ s.2.2)

/-- 概要：標準単体の join の切断は連結した写像から復元できる。
方針：`pullCut_concat` を適用する。
規約：左終域の頂点数 i+1 で切断する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の同型の単射性。 -/
lemma pullCut_stdEncode (i j n : ℕ) (s : Simplex (Δ[i] : SSet.{u}) Δ[j] n) :
    pullCut (stdEncode i j n s) (i + 1) = s.1.val :=
  pullCut_concat _ _ _ _

/-- 概要：標準単体の join の順序写像表示は単射。
方針：切断を逆像で復元し、左右の各頂点で連結写像を評価して両因子を復元する。
規約：切断の等式による移送を先に行う。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の同型。 -/
lemma stdEncode_injective (i j n : ℕ) : Function.Injective (stdEncode.{u} i j n) := by
  intro s t h
  have hc : s.1 = t.1 := Fin.ext (by
    simpa only [pullCut_stdEncode] using congrArg (fun f ↦ pullCut f (i + 1)) h)
  rcases s with ⟨ℓ, x, y⟩
  rcases t with ⟨ℓ', x', y'⟩
  dsimp only at hc
  subst ℓ'
  refine Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · change x = x'
    apply (stdAugEquiv i ℓ.val).injective
    ext a
    have hval := congrArg (fun f : Fin (n + 1) →o Fin ((i + 1) + (j + 1)) ↦
      (f ⟨a.val, lt_of_lt_of_le a.isLt (Nat.le_of_lt_succ ℓ.isLt)⟩).val) h
    dsimp only [stdEncode] at hval
    rw [concat_of_lt _ _ _ _ ⟨a.val, lt_of_lt_of_le a.isLt (Nat.le_of_lt_succ ℓ.isLt)⟩ a.isLt,
      concat_of_lt _ _ _ _ ⟨a.val, lt_of_lt_of_le a.isLt (Nat.le_of_lt_succ ℓ.isLt)⟩ a.isLt] at hval
    exact hval
  · change y = y'
    apply (stdAugEquiv j (n + 1 - ℓ.val)).injective
    ext a
    let b : Fin (n + 1) := ⟨ℓ.val + a.val, by have := a.isLt; omega⟩
    have hb : ℓ.val ≤ b.val := by dsimp [b]; omega
    have hval := congrArg (fun f : Fin (n + 1) →o Fin ((i + 1) + (j + 1)) ↦ (f b).val) h
    dsimp only [stdEncode] at hval
    rw [concat_of_ge _ _ _ _ _ hb, concat_of_ge _ _ _ _ _ hb] at hval
    have ha : (⟨b.val - ℓ.val, by have := b.isLt; omega⟩ : Fin (n + 1 - ℓ.val)) = a :=
      Fin.ext (by dsimp [b]; omega)
    rw [ha] at hval
    omega

/-- 概要：連結した有限順序集合への写像から標準単体の join の単体を復元する。
方針：左終域の逆像を切断とし、左右の制限を標準単体に戻す。
規約：右側の値から左終域の頂点数を引く。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の逆写像。 -/
def stdDecode (i j n : ℕ) (α : Fin (n + 1) →o Fin ((i + 1) + (j + 1))) :
    Simplex (Δ[i] : SSet.{u}) Δ[j] n :=
  ⟨⟨pullCut α (i + 1), by have := pullCut_le α (i + 1); omega⟩,
    (stdAugEquiv i _).symm (leftMap α (i + 1)),
    (stdAugEquiv j _).symm
      { toFun a := ⟨(rightMap α (i + 1) a).val, by
          have := (rightMap α (i + 1) a).isLt
          omega⟩
        monotone' := fun _ _ h ↦ (rightMap α (i + 1)).monotone h }⟩

/-- 概要：分解した標準単体の join の単体を連結すると元の順序写像に戻る。
方針：切断の左右で計算し、右側では引いた頂点数を戻す。
規約：空区間も含む。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の全射性。 -/
lemma stdEncode_stdDecode (i j n : ℕ)
    (α : Fin (n + 1) →o Fin ((i + 1) + (j + 1))) :
    stdEncode i j n (stdDecode.{u} i j n α) = α := by
  ext a
  dsimp only [stdEncode, stdDecode]
  simp only [Equiv.apply_symm_apply]
  by_cases ha : a.val < pullCut α (i + 1)
  · rw [concat_of_lt _ _ _ _ _ ha]
    rfl
  · rw [concat_of_ge _ _ _ _ _ (not_lt.mp ha)]
    change i + 1 + ((α ⟨pullCut α (i + 1) + (a.val - pullCut α (i + 1)), _⟩).val -
      (i + 1)) = (α a).val
    have he : (⟨pullCut α (i + 1) + (a.val - pullCut α (i + 1)),
        by have := a.isLt; omega⟩ : Fin (n + 1)) = a := Fin.ext (by
      change pullCut α (i + 1) + (a.val - pullCut α (i + 1)) = a.val
      omega)
    rw [he]
    have hα : i + 1 ≤ (α a).val := by
      apply Nat.le_of_not_lt
      exact fun h ↦ ha ((lt_pullCut_iff α (i + 1) a).mpr h)
    omega

/-- 概要：標準単体の join の各次数の単体は、連結した有限順序集合への写像と同値。
方針：切断による分解と連結を互いに逆として用いる。
規約：この段階の終域は順序写像の型。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体同型の次数ごとの同値。 -/
def stdSimplexEquiv (i j n : ℕ) : Simplex (Δ[i] : SSet.{u}) Δ[j] n ≃
    (Fin (n + 1) →o Fin ((i + 1) + (j + 1))) where
  toFun := stdEncode i j n
  invFun := stdDecode i j n
  left_inv s := stdEncode_injective i j n (stdEncode_stdDecode i j n (stdEncode i j n s))
  right_inv := stdEncode_stdDecode i j n

/-- 概要：標準単体の join の順序写像表示は単体作用と可換。
方針：切断の逆像の左右で、補った標準単体の引き戻しを計算する。
規約：順序写像の合成は右から左に作用する `comp`。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の同型の自然性。 -/
lemma stdEncode_naturality (i j : ℕ) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Simplex (Δ[i] : SSet.{u}) Δ[j] n) :
    stdEncode i j m (simplexMap Δ[i] Δ[j] α s) = (stdEncode i j n s).comp α := by
  rcases s with ⟨ℓ, x, y⟩
  ext a
  change (concat (pullCut α ℓ.val) (pullCut_le α ℓ.val)
      (stdAugEquiv i _ (augMap Δ[i] (leftMap α ℓ.val) x))
      (stdAugEquiv j _ (augMap Δ[j] (rightMap α ℓ.val) y)) a).val =
    (concat ℓ.val (Nat.le_of_lt_succ ℓ.isLt) (stdAugEquiv i _ x) (stdAugEquiv j _ y) (α a)).val
  by_cases ha : a.val < pullCut α ℓ.val
  · rw [concat_of_lt _ _ _ _ a ha,
      concat_of_lt _ _ _ _ (α a) ((lt_pullCut_iff α ℓ.val a).mp ha), stdAugEquiv_augMap]
    rfl
  · have hα : ℓ.val ≤ (α a).val := by
      apply Nat.le_of_not_lt
      exact fun h ↦ ha ((lt_pullCut_iff α ℓ.val a).mpr h)
    rw [concat_of_ge _ _ _ _ a (not_lt.mp ha), concat_of_ge _ _ _ _ (α a) hα,
      stdAugEquiv_augMap]
    change i + 1 + (stdAugEquiv j _ y
        ⟨(α ⟨pullCut α ℓ.val + (a.val - pullCut α ℓ.val), _⟩).val - ℓ.val, _⟩).val =
      i + 1 + (stdAugEquiv j _ y ⟨(α a).val - ℓ.val, _⟩).val
    have he : (⟨pullCut α ℓ.val + (a.val - pullCut α ℓ.val),
        by have := a.isLt; omega⟩ : Fin (m + 1)) = a := Fin.ext (by
      change pullCut α ℓ.val + (a.val - pullCut α ℓ.val) = a.val
      omega)
    apply congrArg (fun b : Fin (n + 1 - ℓ.val) ↦ i + 1 + (stdAugEquiv j _ y b).val)
    apply Fin.ext
    exact congrArg (fun b : Fin (m + 1) ↦ (α b).val - ℓ.val) he

/-- 概要：連結した終域の頂点数を、標準単体の次数 `i+j+1` に読み替える同値。
方針：有限順序写像を標準単体の単体として表し、頂点数の算術等式で移送する。
規約：移送は頂点の自然数値を保つ。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の標準単体の join の同型。 -/
def stdSimplexTargetEquiv (i j n : ℕ) :
    (Fin (n + 1) →o Fin ((i + 1) + (j + 1))) ≃ (Δ[i + j + 1] : SSet.{u}) _⦋n⦌ where
  toFun f := stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    { toFun a := Fin.cast (by omega) (f a)
      monotone' := fun _ _ h ↦ f.monotone h })
  invFun x :=
    { toFun a := Fin.cast (by omega) (x a)
      monotone' := fun _ _ h ↦ stdSimplex.monotone_apply x h }
  left_inv f := by ext a; rfl
  right_inv x := by apply stdSimplex.ext; intro a; apply Fin.ext; rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：二つの標準単体の join は次数の和に一を足した標準単体と同型。
方針：各次数で左右の順序写像を連結し、逆像による分解を逆写像に取る。
規約：任意の宇宙 u、任意の自然数 i と j に対して構成する。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の錐・slice の標準単体計算。 -/
def joinStdSimplexIso (i j : ℕ) :
    join (Δ[i] : SSet.{u}) Δ[j] ≅ Δ[i + j + 1] :=
  NatIso.ofComponents (fun d ↦
    ((Join.stdSimplexEquiv i j d.unop.len).trans
      (Join.stdSimplexTargetEquiv i j d.unop.len)).toIso)
    (fun α ↦ by
      apply ConcreteCategory.hom_ext
      intro s
      change Join.stdSimplexTargetEquiv i j _
          (Join.stdEncode i j _ (Join.simplexMap Δ[i] Δ[j] α.unop.toOrderHom s)) =
        (Δ[i + j + 1] : SSet.{u}).map α
          (Join.stdSimplexTargetEquiv i j _ (Join.stdEncode i j _ s))
      rw [Join.stdEncode_naturality]
      apply stdSimplex.ext
      intro a
      rfl)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-- 概要：左右の頂点数の和を指定して join の単体を作る。
方針：右側の頂点数を既存の切断表示に移送する。
規約：join の定義は変えず、l+r=n+1 という等式による構成子を補う。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.3（Tag 016K） の coslice の直接評価。 -/
def mkOfSum {K L : SSet.{u}} {n l r : ℕ} (h : l + r = n + 1)
    (a : augObj K l) (b : augObj L r) : Simplex K L n :=
  ⟨⟨l, by omega⟩, a, cast (congrArg (augObj L) (by omega : r = n + 1 - l)) b⟩

/-- 概要：始域と終域の左右の頂点数を指定した右の制限写像。
方針：始域の左頂点数を加え、終域の左頂点数を値から引く。
規約：hc は左区間の逆像の頂点数を指定する。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.3（Tag 016K） の coslice の直接評価の自然性。 -/
def rightMapOfSum {m n l r c d : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hn : l + r = n + 1) (hm : c + d = m + 1) (hc : pullCut α l = c) : Fin d →o Fin r where
  toFun i :=
    let a : Fin (m + 1) := ⟨c + i.val, by have := i.isLt; omega⟩
    ⟨(α a).val - l, by
      have hα : l ≤ (α a).val := by
        apply Nat.le_of_not_lt
        intro h
        have := (lt_pullCut_iff α l a).mpr h
        dsimp [a] at this
        omega
      have := (α a).isLt
      omega⟩
  monotone' i j h := Nat.sub_le_sub_right (α.monotone (Nat.add_le_add_left h c)) l

/-- 概要：左右の頂点数の和を指定した単体の引き戻しの式。
方針：切断の等式と両因子の移送を `Simplex.ext` と `augMap_congr` で扱う。
規約：両方の区間が空になる場合も含む。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.3（Tag 016K） の coslice の普遍性。 -/
lemma simplexMap_mkOfSum (K L : SSet.{u}) {m n l r c d : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hn : l + r = n + 1) (hm : c + d = m + 1)
    (hc : pullCut α l = c) (a : augObj K l) (b : augObj L r) :
    simplexMap K L α (mkOfSum hn a b) =
      mkOfSum hm (augMap K (leftMapAt α l c hc) a) (augMap L (rightMapOfSum α hn hm hc) b) := by
  dsimp only [mkOfSum]
  rw [simplexMap_eq_at K L α _ c hc]
  refine Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · have he : r = n + 1 - l := by omega
    have hd : d = m + 1 - c := by omega
    exact (augMap_congr L hd he (rightMapOfSum α hn hm hc) (rightMapAt α l c hc)
      (fun i j hij ↦ by
        change (α ⟨c + i.val, _⟩).val - l = (α ⟨c + j.val, _⟩).val - l
        exact congrArg (fun z ↦ (α z).val - l) (Fin.ext (by
          change c + i.val = c + j.val
          omega))) b (cast (congrArg (augObj L) he) b) rfl).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-- 概要：補った単体への射の作用は頂点数の等式による移送と可換。
方針：等式で頂点数を置換する。
規約：空の単体も含む。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の左右の頂点数による単体表示。 -/
lemma augHom_cast {K L : SSet.{u}} (f : K ⟶ L) {r s : ℕ} (h : r = s) (a : augObj K r) :
    cast (congrArg (augObj L) h) (augHom f r a) =
      augHom f s (cast (congrArg (augObj K) h) a) := by
  subst s
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：joinMap は左右の頂点数による単体の構成と可換。
方針：切断と左因子を固定し、右因子の移送と射の作用を交換する。
規約：左右の頂点数は空でもよい。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の coslice の直接構成。 -/
lemma joinMap_mkOfSum {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    {n l r : ℕ} (h : l + r = n + 1) (a : Join.augObj K l) (b : Join.augObj L r) :
    (joinMap f g).app (Opposite.op ⦋n⦌) (Join.mkOfSum h a b) =
      Join.mkOfSum h (Join.augHom f l a) (Join.augHom g r b) := by
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · exact (Join.augHom_cast g (by omega : r = n + 1 - l) b).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-- 概要：右区間が空の和による単体表示は左包含に一致する。
方針：切断と左因子を保ち、右因子の一点性を使う。
規約：空の右単体の選択には依存しない。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の coslice の固定条件。 -/
lemma mkOfSum_zero_right {K L : SSet.{u}} {n : ℕ} (h : (n + 1) + 0 = n + 1)
    (k : augObj K (n + 1)) (a : augObj L 0) : mkOfSum h k a = Simplex.inl k := by
  refine Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · exact @Subsingleton.elim (augObj L (n + 1 - (n + 1)))
      (by simp only [Nat.sub_self, augObj]; infer_instance) _ _

/-- 概要：任意の join の単体は左右の頂点数の和による構成子から回収される。
方針：単体の切断と両因子を展開する。
規約：join の元の依存和表示を保つ。
使われ方：HTT §1.2.8、Kerodon §4.3.3（Tag 016K） の直接構成の検証。 -/
lemma mkOfSum_eta {K L : SSet.{u}} {n : ℕ} (s : Simplex K L n) :
    mkOfSum (by have := s.1.isLt; omega : s.1.val + (n + 1 - s.1.val) = n + 1)
      s.2.1 s.2.2 = s := by
  rcases s with ⟨⟨l, hl⟩, a, b⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.8.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex
attribute [cite HTT "1.2.8.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join
attribute [cite HTT "1.2.8.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso
attribute [cite HTT "1.2.8.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join
attribute [cite HTT "1.2.8.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl
attribute [cite HTT "1.2.8.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr
attribute [cite HTT "2.1.4.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join
attribute [cite HTT "2.1.4.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl
attribute [cite HTT "2.1.4.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr

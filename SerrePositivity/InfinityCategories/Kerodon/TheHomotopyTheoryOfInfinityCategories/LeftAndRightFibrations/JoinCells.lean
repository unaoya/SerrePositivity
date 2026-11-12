module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：pushout-join の内 anodyne 性のためのホーンと部分複体の計算。
方針：ホーン・境界セルを標準単体の join の同型で比較し、lifting property で閉包へ広げる。
規約：左の right anodyne、または右の left anodyne を使う。モデル構造は用いない。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の slice の持ち上げ。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet MorphismProperty
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：右 anodyne 射を生成する正次数のホーン包含。
方針：零番目以外の欠けた面を持つホーンを族として指定する。
規約：Λ[n+1,i]、0<i≤n+1。最後の面も許す。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の左因子。 -/
inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) : rightHornInclusions Λ[n + 1, i].ι

/-- 概要：左 anodyne 射を生成する正次数のホーン包含。
方針：最後以外の欠けた面を持つホーンを族として指定する。
規約：Λ[n+1,i]、0≤i<n+1。零番目の面も許す。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の右因子。 -/
inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
      leftHornInclusions Λ[n + 1, i].ι

/-- 概要：右ホーン包含の rlp を持つ全ての射に対し llp を持つ射のクラス。
方針：生成ホーンの rlp の llp として定義する。
規約：right anodyne の意味をモデル構造なしで固定する。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の左因子の仮定。 -/
@[kerodon 0151]
def rightAnodyneExtensions : MorphismProperty SSet.{u} := rightHornInclusions.rlp.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange, IsStableUnderRetracts,
  IsStableUnderTransfiniteComposition, IsStableUnderCoproducts

/-- 概要：左ホーン包含の rlp を持つ全ての射に対し llp を持つ射のクラス。
方針：生成ホーンの rlp の llp として定義する。
規約：left anodyne の意味をモデル構造なしで固定する。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の右因子の仮定。 -/
@[kerodon 014X, kerodon 0151]
def leftAnodyneExtensions : MorphismProperty SSet.{u} := leftHornInclusions.rlp.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange, IsStableUnderRetracts,
  IsStableUnderTransfiniteComposition, IsStableUnderCoproducts

/-- 概要：生成する右ホーン包含は right anodyne。
方針：任意の生成族はその rlp の llp に含まれることを使う。
規約：零番目以外の面。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の基本セル。 -/
lemma rightAnodyneExtensions_horn {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) :
    rightAnodyneExtensions.{u} (horn (n + 1) i).ι :=
  le_llp_rlp _ _ (rightHornInclusions.intro i h0)

/-- 概要：生成する左ホーン包含は left anodyne。
方針：任意の生成族はその rlp の llp に含まれることを使う。
規約：最後以外の面。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の基本セル。 -/
lemma leftAnodyneExtensions_horn {n : ℕ} (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
    leftAnodyneExtensions.{u} (horn (n + 1) i).ι :=
  le_llp_rlp _ _ (leftHornInclusions.intro i hn)

namespace Join

/-- 概要：空単体を補った次数で部分複体に属するという条件。
方針：空区間では真、非空では元の部分複体の所属を使う。
規約：join の純粋に片側だけの単体を含める。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の部分複体の和。 -/
def augMem {K : SSet.{u}} (K₀ : K.Subcomplex) : (r : ℕ) → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r → Prop
  | 0, _ => True
  | r + 1, a => a ∈ K₀.obj (Opposite.op ⦋r⦌)

/-- 概要：補った次数の所属は部分複体の単体として持ち上がることと同値。
方針：空区間では一点、非空では部分型の構成子を使う。
規約：部分複体の包含の像として所属を特徴づける。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の join の像の計算。 -/
lemma augMem_iff_exists {K : SSet.{u}} (K₀ : K.Subcomplex) (r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r) :
    augMem K₀ r a ↔ ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (K₀ : SSet.{u}) r, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom K₀.ι r b = a := by
  cases r with
  | zero =>
    constructor
    · intro _; exact ⟨PUnit.unit, @Subsingleton.elim PUnit inferInstance _ _⟩
    · intro _; trivial
  | succ r =>
    constructor
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨⟨b, hb⟩, h⟩
      change b = a at h
      change a ∈ K₀.obj (Opposite.op ⦋r⦌)
      simpa only [h] using hb

/-- 概要：左部分複体との join への所属は左単体の所属に等しい。
方針：joinMap の像を切断位置ごとに計算する。
規約：空の左区間は常に所属する。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） のセル計算。 -/
lemma mem_joinSubcomplexLeft {A B : SSet.{u}} (A₀ : A.Subcomplex)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft A₀ B).obj (Opposite.op ⦋n⦌) ↔
      augMem A₀ s.1.val s.2.1 := by
  change (∃ t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap A₀.ι (𝟙 B)).app (Opposite.op ⦋n⦌) t = s) ↔ _
  rcases s with ⟨ℓ, a, b⟩
  constructor
  · rintro ⟨⟨c, x, y⟩, h⟩
    have hc : c = ℓ := congrArg Sigma.fst h
    subst c
    have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom A₀.ι ℓ.val x = a := by
      exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h).2)
    exact (augMem_iff_exists A₀ _ _).2 ⟨x, ha⟩
  · intro h
    obtain ⟨x, hx⟩ := (augMem_iff_exists A₀ _ _).1 h
    refine ⟨⟨ℓ, x, b⟩, ?_⟩
    change (⟨ℓ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom A₀.ι ℓ.val x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 B) _ b⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) = _
    rw [hx, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]

/-- 概要：右部分複体との join への所属は右単体の所属に等しい。
方針：joinMap の像を切断位置ごとに計算する。
規約：空の右区間は常に所属する。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） のセル計算。 -/
lemma mem_joinSubcomplexRight {A B : SSet.{u}} (B₀ : B.Subcomplex)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀).obj (Opposite.op ⦋n⦌) ↔
      augMem B₀ (n + 1 - s.1.val) s.2.2 := by
  change (∃ t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) B₀.ι).app (Opposite.op ⦋n⦌) t = s) ↔ _
  rcases s with ⟨ℓ, a, b⟩
  constructor
  · rintro ⟨⟨c, x, y⟩, h⟩
    have hc : c = ℓ := congrArg Sigma.fst h
    subst c
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom B₀.ι (n + 1 - ℓ.val) y = b := by
      exact congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h).2)
    exact (augMem_iff_exists B₀ _ _).2 ⟨y, hb⟩
  · intro h
    obtain ⟨y, hy⟩ := (augMem_iff_exists B₀ _ _).1 h
    refine ⟨⟨ℓ, a, y⟩, ?_⟩
    change (⟨ℓ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 A) _ a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom B₀.ι _ y⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) = _
    rw [hy, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]

/-- 概要：pushout-join の始域への所属は左右いずれかの所属である。
方針：部分複体の和と二つの像の計算を組み合わせる。
規約：空区間も augMem で処理する。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） のセル計算。 -/
lemma mem_joinUnion {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion A₀ B₀).obj (Opposite.op ⦋n⦌) ↔
      augMem A₀ s.1.val s.2.1 ∨ augMem B₀ (n + 1 - s.1.val) s.2.2 := by
  change (s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft A₀ B).obj (Opposite.op ⦋n⦌) ∨
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀).obj (Opposite.op ⦋n⦌)) ↔ _
  rw [mem_joinSubcomplexLeft, mem_joinSubcomplexRight]

/-- 概要：補った標準単体が境界に属する条件は、ある頂点を取らないこと。
方針：空次数は空写像、非空次数は Mathlib の境界の特徴づけに帰着する。
規約：r は頂点数で、r=0 も許す。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の境界セル。 -/
lemma augMem_boundary_iff (p r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[p] : SSet.{u}) r) :
    augMem (boundary p) r a ↔ ∃ v : Fin (p + 1), v ∉ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv p r a) := by
  cases r with
  | zero =>
    constructor
    · intro _; exact ⟨0, by rintro ⟨i, _⟩; exact Fin.elim0 i⟩
    · intro _; trivial
  | succ r => exact mem_boundary_iff_notMem_range a

/-- 概要：補った標準単体がホーンに属する条件は、指定点以外の頂点を取らないこと。
方針：空次数では異なる頂点を選び、非空次数は Mathlib のホーンの特徴づけを使う。
規約：ホーンは正次元 p+1、空次数も含む。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） のホーンセル。 -/
lemma augMem_horn_iff (p r : ℕ) (i : Fin (p + 2))
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[p + 1] : SSet.{u}) r) :
    augMem (horn (p + 1) i) r a ↔
      ∃ v : Fin (p + 2), v ≠ i ∧ v ∉ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv (p + 1) r a) := by
  cases r with
  | zero =>
    constructor
    · intro _
      have hv : ∃ v : Fin (p + 2), v ≠ i := by
        by_cases hi : i = 0
        · exact ⟨Fin.last (p + 1), by intro h; have := congrArg Fin.val (h.trans hi); simp at this⟩
        · exact ⟨0, Ne.symm hi⟩
      obtain ⟨v, hv⟩ := hv
      exact ⟨v, hv, by rintro ⟨j, _⟩; exact Fin.elim0 j⟩
    · intro _; trivial
  | succ r =>
    change (a ∈ (horn (p + 1) i).obj (Opposite.op ⦋r⦌)) ↔ _
    rw [mem_horn_iff_notMem_range]
    simp only [exists_prop]
    rfl

/-- 概要：連結写像が左の頂点を取ることは左写像がその頂点を取ることと同値。
方針：値が左区間にあることから始域も左区間にあると判定する。
規約：頂点は castAdd で連結先に含める。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） のホーンの計算。 -/
lemma mem_range_concat_left {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (v : Fin p) :
    v.castAdd q ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g) ↔ v ∈ Set.range f := by
  constructor
  · rintro ⟨i, hi⟩
    have hleft : i.val < ℓ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_lt_iff ℓ hℓ f g i).1 (by rw [hi]; exact v.isLt)
    refine ⟨⟨i.val, hleft⟩, Fin.ext ?_⟩
    have := congrArg Fin.val hi
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt ℓ hℓ f g i hleft] at this
    exact this
  · rintro ⟨i, hi⟩
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hℓ⟩, Fin.ext ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt ℓ hℓ f g _ i.isLt]
    exact congrArg Fin.val hi

/-- 概要：連結写像が右の頂点を取ることは右写像がその頂点を取ることと同値。
方針：値が右区間にあることから始域の切断以後に制限する。
規約：頂点は natAdd で連結先に含める。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） のホーンの計算。 -/
lemma mem_range_concat_right {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (v : Fin q) :
    v.natAdd p ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g) ↔ v ∈ Set.range g := by
  constructor
  · rintro ⟨i, hi⟩
    have hright : ℓ ≤ i.val := by
      have hn : ¬ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i).val < p := by rw [hi]; change ¬ p + v.val < p; omega
      have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_lt_iff ℓ hℓ f g i).not.1 hn
      omega
    refine ⟨⟨i.val - ℓ, by have := i.isLt; omega⟩, Fin.ext ?_⟩
    have hv := congrArg Fin.val hi
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge ℓ hℓ f g i hright] at hv
    change p + _ = p + v.val at hv
    omega
  · rintro ⟨i, hi⟩
    refine ⟨⟨ℓ + i.val, by have := i.isLt; omega⟩, Fin.ext ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge ℓ hℓ f g _ (by dsimp; omega)]
    change p + (g ⟨ℓ + i.val - ℓ, _⟩).val = p + v.val
    have he : (⟨ℓ + i.val - ℓ, by omega⟩ : Fin (r - ℓ)) = i := by
      apply Fin.ext
      change ℓ + i.val - ℓ = i.val
      omega
    rw [he, hi]

/-- 概要：連結写像で指定頂点以外の欠落がある条件を左右に分解する。
方針：欠落した頂点を二つの連結区間に分け、像の特徴づけを使う。
規約：欠けた頂点 w は連結先の任意の頂点。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の基本セル。 -/
lemma missing_concat_iff {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (w : Fin (p + q)) :
    (∃ v : Fin (p + q), v ≠ w ∧ v ∉ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g)) ↔
      (∃ v : Fin p, v.castAdd q ≠ w ∧ v ∉ Set.range f) ∨
      (∃ v : Fin q, v.natAdd p ≠ w ∧ v ∉ Set.range g) := by
  constructor
  · rintro ⟨v, hv, hm⟩
    by_cases h : v.val < p
    · let a : Fin p := ⟨v.val, h⟩
      have ha : a.castAdd q = v := Fin.ext rfl
      exact Or.inl ⟨a, by rwa [ha], by rwa [← mem_range_concat_left ℓ hℓ f g, ha]⟩
    · let b : Fin q := ⟨v.val - p, by have := v.isLt; omega⟩
      have hb : b.natAdd p = v := Fin.ext (by dsimp [b]; omega)
      exact Or.inr ⟨b, by rwa [hb], by rwa [← mem_range_concat_right ℓ hℓ f g, hb]⟩
  · rintro (⟨v, hv, hm⟩ | ⟨v, hv, hm⟩)
    · exact ⟨v.castAdd q, hv, by rwa [mem_range_concat_left ℓ hℓ f g]⟩
    · exact ⟨v.natAdd p, hv, by rwa [mem_range_concat_right ℓ hℓ f g]⟩

/-- 概要：有限集合の大きさの移送は、指定点以外の欠落の存在を保つ。
方針：大きさの等式で置換する。
規約：始域の大きさは任意で空も許す。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の頂点数の移送。 -/
lemma missing_cast_iff {p q r : ℕ} (h : p = q) (f : Fin r → Fin p) (w : Fin p) :
    (∃ v : Fin q, v ≠ Fin.cast h w ∧ v ∉ Set.range (fun a ↦ Fin.cast h (f a))) ↔
      ∃ v : Fin p, v ≠ w ∧ v ∉ Set.range f := by
  subst q
  rfl

/-- 概要：標準単体の join の同型の下で、ホーンへの所属は連結写像の欠落で判定できる。
方針：標準単体のホーンの特徴づけと有限集合の移送を使う。
規約：指定頂点は連結した頂点集合で与える。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の基本セル。 -/
lemma mem_horn_joinStdSimplexIso_iff (p q n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[p] : SSet.{u}) Δ[q] n) (w : Fin ((p + 1) + (q + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q).hom.app (Opposite.op ⦋n⦌) s ∈
      (horn (p + q + 1) (Fin.cast (by omega) w)).obj (Opposite.op ⦋n⦌) ↔
        ∃ v, v ≠ w ∧ v ∉ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode p q n s) := by
  rw [mem_horn_iff_notMem_range]
  simp only [exists_prop]
  exact missing_cast_iff (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode p q n s) w

/-- 概要：左ホーンと右境界の pushout-join は標準単体のホーンの逆像。
方針：連結した写像で欠ける頂点を左右に分ける。
規約：左ホーンは正次元、右境界は零次元も許す。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の第一の基本セル。 -/
@[kerodon 018N]
lemma horn_boundary_preimage (p q : ℕ) (i : Fin (p + 2)) :
    (horn ((p + 1) + q + 1) (Fin.cast (by omega) (i.castAdd (q + 1)))).preimage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} (p + 1) q).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn (p + 1) i) (boundary q) := by
  ext ⟨⟨n⟩⟩ s
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (p + 1) q).hom.app (Opposite.op ⦋n⦌) s ∈
    (horn ((p + 1) + q + 1) (Fin.cast (by omega) (i.castAdd (q + 1)))).obj _) ↔ _
  rw [mem_horn_joinStdSimplexIso_iff, mem_joinUnion, augMem_horn_iff, augMem_boundary_iff]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode, missing_concat_iff]
  constructor
  · rintro (⟨v, hv, hm⟩ | ⟨v, _, hm⟩)
    · exact Or.inl ⟨v, fun h ↦ hv (congrArg (Fin.castAdd (q + 1)) h), hm⟩
    · exact Or.inr ⟨v, hm⟩
  · rintro (⟨v, hv, hm⟩ | ⟨v, hm⟩)
    · refine Or.inl ⟨v, ?_, hm⟩
      intro h
      apply hv
      apply Fin.ext
      exact congrArg (fun z : Fin ((p + 2) + (q + 1)) ↦ z.val) h
    · refine Or.inr ⟨v, ?_, hm⟩
      intro h
      have he := congrArg Fin.val h
      have hi := i.isLt
      change (p + 1 + 1) + v.val = i.val at he
      omega

/-- 概要：左境界と右ホーンの pushout-join は標準単体のホーンの逆像。
方針：連結した写像で欠ける頂点を左右に分ける。
規約：左境界は零次元も許し、右ホーンは正次元。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の第二の基本セル。 -/
@[kerodon 018N]
lemma boundary_horn_preimage (p q : ℕ) (j : Fin (q + 2)) :
    (horn (p + (q + 1) + 1) (Fin.cast (by omega) (j.natAdd (p + 1)))).preimage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} p (q + 1)).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary p) (horn (q + 1) j) := by
  ext ⟨⟨n⟩⟩ s
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p (q + 1)).hom.app (Opposite.op ⦋n⦌) s ∈
    (horn (p + (q + 1) + 1) (Fin.cast (by omega) (j.natAdd (p + 1)))).obj _) ↔ _
  rw [mem_horn_joinStdSimplexIso_iff, mem_joinUnion, augMem_boundary_iff, augMem_horn_iff]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode, missing_concat_iff]
  constructor
  · rintro (⟨v, _, hm⟩ | ⟨v, hv, hm⟩)
    · exact Or.inl ⟨v, hm⟩
    · exact Or.inr ⟨v, fun h ↦ hv (congrArg (Fin.natAdd (p + 1)) h), hm⟩
  · rintro (⟨v, hm⟩ | ⟨v, hv, hm⟩)
    · refine Or.inl ⟨v, ?_, hm⟩
      intro h
      have he := congrArg (fun z : Fin ((p + 1) + (q + 2)) ↦ z.val) h
      have hv := v.isLt
      change v.val = (p + 1) + j.val at he
      omega
    · refine Or.inr ⟨v, ?_, hm⟩
      intro h
      apply hv
      apply Fin.ext
      have he := congrArg (fun z : Fin ((p + 1) + (q + 2)) ↦ z.val) h
      change (p + 1) + v.val = (p + 1) + j.val at he
      omega

end Join

/-- 概要：同型に沿う部分複体の逆像は元の部分複体と同型。
方針：次数ごとに元の同型と逆写像を部分型へ制限する。
規約：同型の向きは逆像から元へ。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） のホーン包含の移送。 -/
def subcomplexPreimageIso {X Y : SSet.{u}} (B : Y.Subcomplex) (e : X ≅ Y) :
    (B.preimage e.hom : SSet.{u}) ≅ (B : SSet.{u}) where
  hom := B.fromPreimage e.hom
  inv :=
    { app n := ↾fun b ↦ ⟨e.inv.app n b.val, by
        change e.hom.app n (e.inv.app n b.val) ∈ B.obj n
        simpa only [← NatTrans.comp_app_apply, e.inv_hom_id, NatTrans.id_app,
          types_id_apply] using b.property⟩
      naturality {m n} α := by
        apply ConcreteCategory.hom_ext
        intro b
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (e.inv.naturality α) b.val }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro b
    apply Subtype.ext
    change e.inv.app n (e.hom.app n b.val) = b.val
    simp only [← NatTrans.comp_app_apply, e.hom_inv_id, NatTrans.id_app,
      types_id_apply]
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro b
    apply Subtype.ext
    change e.hom.app n (e.inv.app n b.val) = b.val
    simp only [← NatTrans.comp_app_apply, e.inv_hom_id, NatTrans.id_app,
      types_id_apply]

/-- 概要：同型に沿う逆像の包含が inner anodyne であることは元の包含と同値。
方針：部分複体の同型と標的の同型で矢の同型を作る。
規約：モデル構造を用いず同型不変性だけを使う。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の基本セル。 -/
lemma innerAnodyne_preimage_iff {X Y : SSet.{u}} (B : Y.Subcomplex) (e : X ≅ Y) :
    innerAnodyneExtensions (B.preimage e.hom).ι ↔ innerAnodyneExtensions B.ι :=
  innerAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (subcomplexPreimageIso B e) e (by rfl))

/-- 概要：右ホーンと境界の pushout-join の包含は inner anodyne。
方針：標準単体の同型で、欠けた面が内点のホーン包含に移す。
規約：左は Λ[p+1,i]、0<i。右は ∂Δ[q]、q≥0。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の第一の生成セル。 -/
@[kerodon 018N]
lemma joinUnion_rightHorn_boundary_innerAnodyne (p q : ℕ) (i : Fin (p + 2)) (h0 : 0 < i) :
    innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn (p + 1) i) (boundary q)).ι := by
  rw [← Join.horn_boundary_preimage, innerAnodyne_preimage_iff]
  apply innerAnodyneExtensions.horn_ι
  · change 0 < i.val
    exact h0
  · change i.val < (p + 1) + q + 1
    have := i.isLt
    omega

/-- 概要：境界と左ホーンの pushout-join の包含は inner anodyne。
方針：標準単体の同型で、欠けた面が内点のホーン包含に移す。
規約：左は ∂Δ[p]、右は Λ[q+1,j]、j<q+1。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4（Tag 018J） の第二の生成セル。 -/
@[kerodon 018N]
lemma joinUnion_boundary_leftHorn_innerAnodyne (p q : ℕ) (j : Fin (q + 2))
    (hn : j < Fin.last (q + 1)) :
    innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary p) (horn (q + 1) j)).ι := by
  rw [← Join.boundary_horn_preimage, innerAnodyne_preimage_iff]
  apply innerAnodyneExtensions.horn_ι
  · change 0 < (p + 1) + j.val
    omega
  · change (p + 1) + j.val < p + (q + 1) + 1
    have hj : j.val < q + 1 := hn
    omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

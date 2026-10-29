module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Order.WithBot
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Flat.Basic

/-! # 代数図式の添字変更と終段の追加

## 概要

`B` 代数の図式（段の環 `S i` と遷移写像 `f i j : S i →ₐ[B] S j`）について、剰余体拡大の超限構成で
使う三つの操作を、遷移写像を具体的に定義して与える。
- 単調な添字写像による引き戻し（`algebraSystemReindexMap`）。
- `WithTop` による新しい終段 `T` の追加（`algebraSystemWithTopObj`、`algebraSystemWithTopMap`）。
- 開初期部分 `{j // j < i}` 上の図式に終段を加えて、閉初期部分 `{j // j ≤ i}` 上の図式にする
  （`algebraInitialSegmentObj`、`algebraInitialSegmentMap`）。順序同型
  `WithTop {j // j < i} ≃o {j // j ≤ i}`（`initialSegmentWithTopEquiv`）を通して移す。

## 方針

それぞれの操作で、有向図式の法則（`DirectedSystem`）、各段の局所性・平坦性・基底からの写像の局所性、
基底の極大イデアルの拡張、指定終域 `K` への写像の両立を保存することを確かめる。
段の取り違えは `HEq` で述べる。

## 規約

図式は関数の組で表し、構造体にはまとめない（構造体版は `ResidueFieldExtension/Diagram`）。
二つの表し方の一本化は剰余体拡大の構成を書き直すときに行う。

## 使われ方

剰余体拡大の構成（`ResidueFieldClosedExtension`、`ResidueFieldBeforeExtension`、
`ResidueFieldExtension/Diagram`）。
-/

@[expose] public section

namespace SerrePositivity

section Reindex

variable {B ι κ : Type*} [CommRing B] [Preorder ι] [Preorder κ]
variable (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable (f : ∀ i j, i ≤ j → S i →ₐ[B] S j)
variable (r : κ → ι) (hr : Monotone r)

/-- 添字が等しければ、源と終域の型も含めて遷移写像が一致する。
順序の証明引数は証明無関係性で同一視される。 -/
theorem algebraSystemMap_heq_of_eq {i j i' j' : ι}
    (hi : i = i') (hj : j = j') (h : i ≤ j) (h' : i' ≤ j') :
    HEq (f i j h) (f i' j' h') := by
  cases hi
  cases hj
  rfl

/-- 単調な添字写像に沿って遷移写像を引き戻す。 -/
def algebraSystemReindexMap : ∀ i j, i ≤ j → S (r i) →ₐ[B] S (r j) :=
  fun i j h ↦ f (r i) (r j) (hr h)

/-- 有向図式の法則は添字変更で保持される。添字写像の単射性は不要。 -/
theorem algebraSystemReindex_directedSystem [DirectedSystem S (f · · ·)] :
    DirectedSystem (fun i ↦ S (r i)) (algebraSystemReindexMap S f r hr · · ·) := by
  constructor
  · intro i x
    exact DirectedSystem.map_self' (f := f) x
  · intro k j i hij hjk x
    exact DirectedSystem.map_map' (f := f) (hr hij) (hr hjk) x

/-- 局所な遷移写像は制限しても局所である。 -/
theorem algebraSystemReindex_isLocalHom
    (hf : ∀ i j h, IsLocalHom (f i j h).toRingHom) :
    ∀ i j h, IsLocalHom (algebraSystemReindexMap S f r hr i j h).toRingHom :=
  fun i j h ↦ hf (r i) (r j) (hr h)

section Target
variable {K : Type*} [CommRing K] [Algebra B K]
variable (g : ∀ i, S i →ₐ[B] K)
variable (hg : ∀ i j h x, g j (f i j h x) = g i x)

omit [Preorder ι] in
/-- 源の添字が等しければ、指定終域への写像も型の同一視を含めて一致する。 -/
theorem algebraSystemTarget_heq_of_eq {i j : ι} (h : i = j) : HEq (g i) (g j) := by
  cases h
  rfl

include hg in
/-- 指定終域への写像の両立は制限で保持される。 -/
theorem algebraSystemReindexTarget_compatible :
    ∀ i j h x, g (r j) (algebraSystemReindexMap S f r hr i j h x) = g (r i) x :=
  fun i j h x ↦ hg (r i) (r j) (hr h) x

end Target

end Reindex

section WithTop

universe u
variable {B ι : Type*} [CommRing B] [Preorder ι]
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable (T : Type u) [CommRing T] [Algebra B T]

/-- 新しい終段Tを持つ段の族。 -/
def algebraSystemWithTopObj : WithTop ι → Type u
  | none => T
  | some i => S i

instance (i : WithTop ι) : CommRing (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (CommRing T)
  | some j => inferInstanceAs (CommRing (S j))

instance (i : WithTop ι) : Algebra B (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (Algebra B T)
  | some j => inferInstanceAs (Algebra B (S j))

instance algebraSystemWithTop_local [∀ i, IsLocalRing (S i)] [IsLocalRing T]
    (i : WithTop ι) : IsLocalRing (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (IsLocalRing T)
  | some j => inferInstanceAs (IsLocalRing (S j))

instance algebraSystemWithTop_flat [∀ i, Module.Flat B (S i)] [Module.Flat B T]
    (i : WithTop ι) : Module.Flat B (algebraSystemWithTopObj S T i) :=
  match i with
  | none => inferInstanceAs (Module.Flat B T)
  | some j => inferInstanceAs (Module.Flat B (S j))

instance algebraSystemWithTop_baseLocal [∀ i, IsLocalHom (algebraMap B (S i))]
    [IsLocalHom (algebraMap B T)] (i : WithTop ι) :
    IsLocalHom (algebraMap B (algebraSystemWithTopObj S T i)) :=
  match i with
  | none => inferInstanceAs (IsLocalHom (algebraMap B T))
  | some j => inferInstanceAs (IsLocalHom (algebraMap B (S j)))

omit [Preorder ι] in
/-- 極大イデアルが基底の拡張であることを、追加した終段を含む全段で保持する。 -/
theorem algebraSystemWithTop_maximalIdeal_map [IsLocalRing B]
    [∀ i, IsLocalRing (S i)] [IsLocalRing T]
    (hS : ∀ i, (IsLocalRing.maximalIdeal B).map (algebraMap B (S i)) =
      IsLocalRing.maximalIdeal (S i))
    (hT : (IsLocalRing.maximalIdeal B).map (algebraMap B T) = IsLocalRing.maximalIdeal T) :
    ∀ i, (IsLocalRing.maximalIdeal B).map (algebraMap B (algebraSystemWithTopObj S T i)) =
      IsLocalRing.maximalIdeal (algebraSystemWithTopObj S T i) := by
  intro i
  cases i with
  | top => exact hT
  | coe j => exact hS j

variable (f : ∀ i j, i ≤ j → S i →ₐ[B] S j) [DirectedSystem S (f · · ·)]
variable (c : ∀ i, S i →ₐ[B] T)
variable (hc : ∀ i j h x, c j (f i j h x) = c i x)

/-- 旧段どうしはf、旧段から新終段へはc、新終段の自己写像は恒等写像。 -/
def algebraSystemWithTopMap :
    ∀ i j, i ≤ j → algebraSystemWithTopObj S T i →ₐ[B] algebraSystemWithTopObj S T j
  | some i, some j, h => f i j (WithTop.coe_le_coe.mp h)
  | some i, none, _ => c i
  | none, none, _ => AlgHom.id B T
  | none, some j, h => False.elim (WithTop.not_top_le_coe j h)

include hc in
/-- 新終段を加えた遷移写像は、実際に有向図式の法則を満たす。 -/
theorem algebraSystemWithTop_directedSystem :
    DirectedSystem (algebraSystemWithTopObj S T) (algebraSystemWithTopMap S T f c · · ·) := by
  constructor
  · intro i x
    cases i with
    | top => rfl
    | coe i => exact DirectedSystem.map_self' (f := f) x
  · intro k j i hij hjk x
    cases i with
    | top =>
      have hj : j = ⊤ := WithTop.top_le_iff.mp hij
      subst j
      have hk : k = ⊤ := WithTop.top_le_iff.mp hjk
      subst k
      rfl
    | coe i =>
      cases j with
      | top =>
        have hk : k = ⊤ := WithTop.top_le_iff.mp hjk
        subst k
        rfl
      | coe j =>
        cases k with
        | top => exact hc i j (WithTop.coe_le_coe.mp hij) x
        | coe k =>
          exact DirectedSystem.map_map' (f := f)
            (WithTop.coe_le_coe.mp hij) (WithTop.coe_le_coe.mp hjk) x

omit [DirectedSystem S (f · · ·)] in
/-- 旧遷移と新終段への写像が局所なら、追加後の遷移も局所である。 -/
theorem algebraSystemWithTopMap_isLocalHom
    (hf : ∀ i j h, IsLocalHom (f i j h).toRingHom)
    (hcLocal : ∀ i, IsLocalHom (c i).toRingHom) :
    ∀ i j h, IsLocalHom (algebraSystemWithTopMap S T f c i j h).toRingHom := by
  intro i j h
  cases i with
  | top =>
    have hj : j = ⊤ := WithTop.top_le_iff.mp h
    subst j
    exact inferInstanceAs (IsLocalHom (RingHom.id T))
  | coe i =>
    cases j with
    | top => exact hcLocal i
    | coe j => exact hf i j (WithTop.coe_le_coe.mp h)

section Target
variable {K : Type*} [CommRing K] [Algebra B K]
variable (g : ∀ i, S i →ₐ[B] K) (gT : T →ₐ[B] K)
variable (hg : ∀ i j h x, g j (f i j h x) = g i x)
variable (hgc : ∀ i x, gT (c i x) = g i x)

/-- 追加した終段を含む、指定終域への段写像。 -/
def algebraSystemWithTopTarget : ∀ i, algebraSystemWithTopObj S T i →ₐ[B] K
  | none => gT
  | some i => g i

omit [DirectedSystem S (f · · ·)] in
include hg hgc in
/-- 新終段の写像が旧段の写像と両立すれば、追加後も全ての段で両立する。 -/
theorem algebraSystemWithTopTarget_compatible :
    ∀ i j h x, algebraSystemWithTopTarget S T g gT j
      (algebraSystemWithTopMap S T f c i j h x) = algebraSystemWithTopTarget S T g gT i x := by
  intro i j h x
  cases i with
  | top =>
    have hj : j = ⊤ := WithTop.top_le_iff.mp h
    subst j
    rfl
  | coe i =>
    cases j with
    | top => exact hgc i x
    | coe j => exact hg i j (WithTop.coe_le_coe.mp h) x

end Target

end WithTop

section InitialSegmentWithTop

variable {ι : Type*} [LinearOrder ι]

/-- 開初期部分に終点を追加した添字を、閉初期部分へ送る。 -/
def initialSegmentWithTopMap (i : ι) : WithTop {j : ι // j < i} → {j : ι // j ≤ i} :=
  WithTop.recTopCoe ⟨i, le_rfl⟩ (fun j ↦ ⟨j.val, j.property.le⟩)

@[simp] theorem initialSegmentWithTopMap_top (i : ι) :
    initialSegmentWithTopMap i ⊤ = ⟨i, le_rfl⟩ := rfl

@[simp] theorem initialSegmentWithTopMap_coe (i : ι) (j : {j : ι // j < i}) :
    initialSegmentWithTopMap i (j : WithTop {j : ι // j < i}) = ⟨j.val, j.property.le⟩ := rfl

/-- 閉初期部分の終点をtopへ、それ以外を旧添字へ戻す。 -/
def initialSegmentWithTopInv (i : ι) (j : {j : ι // j ≤ i}) : WithTop {j : ι // j < i} :=
  if h : j.val = i then ⊤ else (⟨j.val, lt_of_le_of_ne j.property h⟩ : {j : ι // j < i})

/-- WithTop(Iio i)をIic iへ移す具体的な順序同型。 -/
def initialSegmentWithTopEquiv (i : ι) :
    WithTop ({j : ι // j < i}) ≃o {j : ι // j ≤ i} where
  toFun := initialSegmentWithTopMap i
  invFun := initialSegmentWithTopInv i
  left_inv x := by
    cases x with
    | top =>
      rw [initialSegmentWithTopMap_top]
      unfold initialSegmentWithTopInv
      rw [dite_eq_left rfl]
    | coe j =>
      rw [initialSegmentWithTopMap_coe]
      unfold initialSegmentWithTopInv
      rw [dite_eq_right j.property.ne]
  right_inv j := by
    unfold initialSegmentWithTopInv
    by_cases h : j.val = i
    · rw [dite_eq_left h, initialSegmentWithTopMap_top]
      exact Subtype.ext h.symm
    · rw [dite_eq_right h, initialSegmentWithTopMap_coe]
  map_rel_iff' := by
    intro x y
    cases x with
    | top =>
      cases y with
      | top => simp
      | coe j =>
        change i ≤ j.val ↔ (⊤ : WithTop ({j : ι // j < i})) ≤ ↑j
        simp only [WithTop.not_top_le_coe, iff_false]
        exact not_le_of_gt j.property
    | coe j =>
      cases y with
      | top =>
        change j.val ≤ i ↔ (j : WithTop ({j : ι // j < i})) ≤ ⊤
        exact iff_of_true j.property.le le_top
      | coe k =>
        change j ≤ k ↔ (j : WithTop ({j : ι // j < i})) ≤ k
        exact WithTop.coe_le_coe.symm

@[simp] theorem initialSegmentWithTopEquiv_top (i : ι) :
    initialSegmentWithTopEquiv i ⊤ = ⟨i, le_rfl⟩ := rfl

@[simp] theorem initialSegmentWithTopEquiv_coe (i : ι) (j : {j : ι // j < i}) :
    initialSegmentWithTopEquiv i (j : WithTop ({j : ι // j < i})) = ⟨j.val, j.property.le⟩ := rfl

@[simp] theorem initialSegmentWithTopEquiv_symm_top (i : ι) :
    (initialSegmentWithTopEquiv i).symm ⟨i, le_rfl⟩ = ⊤ := by
  exact (initialSegmentWithTopEquiv i).symm_apply_apply ⊤

@[simp] theorem initialSegmentWithTopEquiv_symm_coe (i : ι) (j : {j : ι // j < i}) :
    (initialSegmentWithTopEquiv i).symm ⟨j.val, j.property.le⟩ =
      (j : WithTop ({j : ι // j < i})) := by
  exact (initialSegmentWithTopEquiv i).symm_apply_apply j

end InitialSegmentWithTop

section InitialSegment

universe u
variable {B ι : Type*} [CommRing B] [LinearOrder ι]
variable (i : ι) (S : {j : ι // j < i} → Type u)
variable [∀ j, CommRing (S j)] [∀ j, Algebra B (S j)]
variable (T : Type u) [CommRing T] [Algebra B T]

/-- 開初期部分の旧段と新しい終段を、閉初期部分の上に置く。 -/
def algebraInitialSegmentObj (j : {j : ι // j ≤ i}) : Type u :=
  algebraSystemWithTopObj S T ((initialSegmentWithTopEquiv i).symm j)

instance (j : {j : ι // j ≤ i}) : CommRing (algebraInitialSegmentObj i S T j) :=
  inferInstanceAs (CommRing (algebraSystemWithTopObj S T ((initialSegmentWithTopEquiv i).symm j)))

instance (j : {j : ι // j ≤ i}) : Algebra B (algebraInitialSegmentObj i S T j) :=
  inferInstanceAs (Algebra B (algebraSystemWithTopObj S T ((initialSegmentWithTopEquiv i).symm j)))

instance algebraInitialSegment_local [∀ j, IsLocalRing (S j)] [IsLocalRing T]
    (j : {j : ι // j ≤ i}) :
    IsLocalRing (algebraInitialSegmentObj i S T j) :=
  inferInstanceAs (IsLocalRing
    (algebraSystemWithTopObj S T ((initialSegmentWithTopEquiv i).symm j)))

instance algebraInitialSegment_flat [∀ j, Module.Flat B (S j)] [Module.Flat B T]
    (j : {j : ι // j ≤ i}) :
    Module.Flat B (algebraInitialSegmentObj i S T j) :=
  inferInstanceAs (Module.Flat B
    (algebraSystemWithTopObj S T ((initialSegmentWithTopEquiv i).symm j)))

instance algebraInitialSegment_baseLocal [∀ j, IsLocalHom (algebraMap B (S j))]
    [IsLocalHom (algebraMap B T)] (j : {j : ι // j ≤ i}) :
    IsLocalHom (algebraMap B (algebraInitialSegmentObj i S T j)) :=
  inferInstanceAs (IsLocalHom (algebraMap B
    (algebraSystemWithTopObj S T ((initialSegmentWithTopEquiv i).symm j))))

/-- 各段の極大イデアル等式は、閉初期部分へ移しても保持される。 -/
theorem algebraInitialSegment_maximalIdeal_map [IsLocalRing B]
    [∀ j, IsLocalRing (S j)] [IsLocalRing T]
    (hS : ∀ j, (IsLocalRing.maximalIdeal B).map (algebraMap B (S j)) =
      IsLocalRing.maximalIdeal (S j))
    (hT : (IsLocalRing.maximalIdeal B).map (algebraMap B T) = IsLocalRing.maximalIdeal T) :
    ∀ j, (IsLocalRing.maximalIdeal B).map (algebraMap B (algebraInitialSegmentObj i S T j)) =
      IsLocalRing.maximalIdeal (algebraInitialSegmentObj i S T j) :=
  fun j ↦ algebraSystemWithTop_maximalIdeal_map S T hS hT ((initialSegmentWithTopEquiv i).symm j)

omit [∀ j, CommRing (S j)] [CommRing T] in
@[simp] theorem algebraInitialSegmentObj_last : algebraInitialSegmentObj i S T ⟨i, le_rfl⟩ = T := by
  simp only [algebraInitialSegmentObj, initialSegmentWithTopEquiv_symm_top]
  rfl

omit [∀ j, CommRing (S j)] [CommRing T] in
@[simp] theorem algebraInitialSegmentObj_old (j : {j : ι // j < i}) :
    algebraInitialSegmentObj i S T ⟨j.val, j.property.le⟩ = S j := by
  simp only [algebraInitialSegmentObj, initialSegmentWithTopEquiv_symm_coe]
  rfl

variable (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) (c : ∀ j, S j →ₐ[B] T)

/-- 閉初期部分の遷移写像。 -/
def algebraInitialSegmentMap :
    ∀ j k, j ≤ k → algebraInitialSegmentObj i S T j →ₐ[B] algebraInitialSegmentObj i S T k :=
  fun j k h ↦ algebraSystemWithTopMap S T f c
    ((initialSegmentWithTopEquiv i).symm j) ((initialSegmentWithTopEquiv i).symm k)
    ((initialSegmentWithTopEquiv i).symm.monotone h)

/-- 旧遷移写像は、閉初期部分への延長後も同じ代数写像である。
源・終域の添字が異なるためHEqで表し、型の同一視も含めて一致を確認する。 -/
theorem algebraInitialSegmentMap_old (j k : {j : ι // j < i}) (h : j ≤ k) :
    HEq (algebraInitialSegmentMap i S T f c ⟨j.val, j.property.le⟩ ⟨k.val, k.property.le⟩ h)
      (f j k h) := by
  exact algebraSystemMap_heq_of_eq (algebraSystemWithTopObj S T)
    (algebraSystemWithTopMap S T f c)
    (initialSegmentWithTopEquiv_symm_coe i j) (initialSegmentWithTopEquiv_symm_coe i k)
    ((initialSegmentWithTopEquiv i).symm.monotone h) (WithTop.coe_le_coe.mpr h)

/-- 旧図式の法則と両立する終段への写像から、閉初期部分の図式を構成する。 -/
theorem algebraInitialSegment_directedSystem [DirectedSystem S (f · · ·)]
    (hc : ∀ j k h x, c k (f j k h x) = c j x) :
    DirectedSystem (algebraInitialSegmentObj i S T) (algebraInitialSegmentMap i S T f c · · ·) := by
  let : DirectedSystem (algebraSystemWithTopObj S T) (algebraSystemWithTopMap S T f c · · ·) :=
    algebraSystemWithTop_directedSystem S T f c hc
  exact algebraSystemReindex_directedSystem (algebraSystemWithTopObj S T)
    (algebraSystemWithTopMap S T f c)
    (initialSegmentWithTopEquiv i).symm (initialSegmentWithTopEquiv i).symm.monotone

/-- 局所な遷移写像は添字の移し替え後も局所である。 -/
theorem algebraInitialSegmentMap_isLocalHom
    (hf : ∀ j k h, IsLocalHom (f j k h).toRingHom)
    (hc : ∀ j, IsLocalHom (c j).toRingHom) :
    ∀ j k h, IsLocalHom (algebraInitialSegmentMap i S T f c j k h).toRingHom := by
  apply algebraSystemReindex_isLocalHom
  exact algebraSystemWithTopMap_isLocalHom S T f c hf hc

section Target
variable {K : Type*} [CommRing K] [Algebra B K]
variable (g : ∀ j, S j →ₐ[B] K) (gT : T →ₐ[B] K)

/-- 指定終域への写像を閉初期部分へ移す。 -/
def algebraInitialSegmentTarget : ∀ j, algebraInitialSegmentObj i S T j →ₐ[B] K :=
  fun j ↦ algebraSystemWithTopTarget S T g gT ((initialSegmentWithTopEquiv i).symm j)

/-- 指定終域への旧段の写像を保持する。 -/
theorem algebraInitialSegmentTarget_old (j : {j : ι // j < i}) :
    HEq (algebraInitialSegmentTarget i S T g gT ⟨j.val, j.property.le⟩) (g j) := by
  exact algebraSystemTarget_heq_of_eq (algebraSystemWithTopObj S T)
    (algebraSystemWithTopTarget S T g gT) (initialSegmentWithTopEquiv_symm_coe i j)

/-- 終域への写像の像も旧段では変わらない。 -/
theorem algebraInitialSegmentTarget_range_old (j : {j : ι // j < i}) :
    Set.range (algebraInitialSegmentTarget i S T g gT ⟨j.val, j.property.le⟩) = Set.range (g j) :=
  congrArg (fun x ↦ Set.range (algebraSystemWithTopTarget S T g gT x))
    (initialSegmentWithTopEquiv_symm_coe i j)

/-- 新終段の像は、その写像gTの像である。 -/
theorem algebraInitialSegmentTarget_range_last :
    Set.range (algebraInitialSegmentTarget i S T g gT ⟨i, le_rfl⟩) = Set.range gT :=
  congrArg (fun x ↦ Set.range (algebraSystemWithTopTarget S T g gT x))
    (initialSegmentWithTopEquiv_symm_top i)

/-- 終域への両立も閉初期部分への移し替えで保持する。 -/
theorem algebraInitialSegmentTarget_compatible
    (hg : ∀ j k h x, g k (f j k h x) = g j x)
    (hgc : ∀ j x, gT (c j x) = g j x) :
    ∀ j k h x, algebraInitialSegmentTarget i S T g gT k
      (algebraInitialSegmentMap i S T f c j k h x) =
        algebraInitialSegmentTarget i S T g gT j x := by
  intro j k h x
  exact algebraSystemWithTopTarget_compatible S T f c g gT hg hgc
    ((initialSegmentWithTopEquiv i).symm j) ((initialSegmentWithTopEquiv i).symm k)
    ((initialSegmentWithTopEquiv i).symm.monotone h) x

end Target

end InitialSegment

end SerrePositivity

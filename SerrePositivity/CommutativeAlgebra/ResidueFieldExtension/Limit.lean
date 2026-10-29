module

public import SerrePositivity.CommutativeAlgebra.DirectLimit
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.SetTheory.Cardinal.Order
public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.Simple

/-! # 剰余体拡大の直極限の段

## 概要

剰余体拡大の超限構成のうち、極限の段に関わる部分を集める。
- 平坦局所拡大の有向図式の直極限は、`m_B` の拡張が極大イデアルとなる平坦局所拡大で、
  指定体 `K` への両立する写像が `K` 全体を覆えば、直極限の剰余体は `K` と同一視される
  （`ResidueFieldDirectLimit`）。
- 指定体 `K` の生成元を整列させた添字（`ResidueFieldGeneratorIndex`）と、初期部分が生成する中間体の
  包含・一元追加・合併・被覆。
- 各段から `K` への写像（`residueFieldStageMap`）と、開初期部分の極限での指定剰余体
  （`ResidueFieldBeforeLimit`）。中間体への値の制限は Mathlib の `AlgHom.codRestrict` で行う。

## 方針

直極限の局所性・平坦性は `CommutativeAlgebra/DirectLimit` から取る。剰余体の比較は、
直極限の元が有限の段で代表されることと、中間体の有向合併（`IntermediateField.coe_iSup_of_directed`）による。

## 規約

添字は `K` 自身に入れた整列で、添字と各初期部分は `K` と同じ宇宙に収まる。順序体構造は要求しない。

## 使われ方

閉初期部分の延長（`ResidueFieldExtension/Step`）と最終定理（`ResidueFieldExtension/General`）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section DirectLimit

open IsLocalRing
variable {B ι : Type*} [CommRing B] [IsLocalRing B]
variable [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
variable [∀ i, Algebra B (S i)]
variable (f : ∀ i j, i ≤ j → S i →ₐ[B] S j) [DirectedSystem S (f · · ·)]

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 基底から直極限への係数写像は、どの段を経由しても同じ写像である。 -/
theorem directLimit_algebraMap_comp (i : ι) :
    (DirectLimit.Ring.of S f i).comp (algebraMap B (S i)) =
      algebraMap B (DirectLimit S f) := by
  ext b
  exact (DirectLimit.Algebra.of S f i).commutes b

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 局所な遷移写像と局所な係数写像の直極限では、基底の係数写像も局所。 -/
theorem directLimit_algebraMap_isLocalHom
    [∀ i, IsLocalHom (algebraMap B (S i))]
    (hlocal : ∀ i j h, IsLocalHom (f i j h).toRingHom) :
    IsLocalHom (algebraMap B (DirectLimit S f)) := by
  let i := Classical.arbitrary ι
  let : IsLocalHom (DirectLimit.Ring.of S f i) := directLimit_isLocalHom S f hlocal i
  rw [← directLimit_algebraMap_comp S f i]
  infer_instance

/-- 各段で基底の極大イデアルを拡張していれば、直極限でも同じ等式が成立する。
極大イデアルの有限生成性・Noether性は不要。 -/
theorem directLimit_maximalIdeal_map
    [∀ i, IsLocalHom (algebraMap B (S i))]
    (hlocal : ∀ i j h, IsLocalHom (f i j h).toRingHom)
    (hmax : ∀ i, (maximalIdeal B).map (algebraMap B (S i)) = maximalIdeal (S i))
    [IsLocalRing (DirectLimit S f)] :
    (maximalIdeal B).map (algebraMap B (DirectLimit S f)) = maximalIdeal (DirectLimit S f) := by
  let : IsLocalHom (algebraMap B (DirectLimit S f)) :=
    directLimit_algebraMap_isLocalHom S f hlocal
  refine le_antisymm (IsLocalRing.map_maximalIdeal_le _) ?_
  intro x hx
  obtain ⟨i, a, ha⟩ := DirectLimit.exists_eq_mk f x
  have ha' : DirectLimit.Ring.of S f i a = x := by with_unfolding_all exact ha.symm
  have ham : a ∈ maximalIdeal (S i) := fun hu ↦ hx (ha' ▸ hu.map (DirectLimit.Ring.of S f i))
  rw [← hmax i] at ham
  have hm := Ideal.mem_map_of_mem (DirectLimit.Ring.of S f i) ham
  rw [Ideal.map_map, directLimit_algebraMap_comp S f i, ha'] at hm
  exact hm

section Residue
variable {K : Type*} [Field K] [Algebra B K]
variable (g : ∀ i, S i →ₐ[B] K)
variable (hg : ∀ i j h x, g j (f i j h x) = g i x)
variable (hcover : ∀ x : K, ∃ i, ∃ y : S i, g i y = x)

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
include hcover in
/-- 体全体を覆う両立する段写像は、直極限からの全射を与える。 -/
theorem directLimit_fieldLift_surjective :
    Function.Surjective (DirectLimit.Algebra.lift S f K g hg) := by
  intro x
  obtain ⟨i, y, hy⟩ := hcover x
  exact ⟨DirectLimit.Algebra.of S f i y, hy⟩

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 指定体を覆う図式の直極限の剰余体同型。
局所性は別に供給し、適用の入口では局所環の保存定理を使う。 -/
noncomputable def directLimitResidueEquiv [IsLocalRing (DirectLimit S f)] :
    ResidueField (DirectLimit S f) ≃+* K := by
  let G := (DirectLimit.Algebra.lift S f K g hg).toRingHom
  have hsurj : Function.Surjective G := directLimit_fieldLift_surjective S f g hg hcover
  have hker : RingHom.ker G = maximalIdeal (DirectLimit S f) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective G hsurj)
  exact (Ideal.quotEquivOfEq hker.symm).trans (G.quotientKerEquivOfSurjective hsurj)

omit [IsLocalRing B] [∀ i, IsLocalRing (S i)] in
/-- 剰余体同型は、各段の元に対して元の指定体への写像と一致する。 -/
@[simp] theorem directLimitResidueEquiv_of [IsLocalRing (DirectLimit S f)] (i : ι) (x : S i) :
    directLimitResidueEquiv S f g hg hcover
      (residue (DirectLimit S f) (DirectLimit.Ring.of S f i x)) = g i x := by
  simp only [directLimitResidueEquiv, residue]
  rfl

omit [∀ i, IsLocalRing (S i)] in
/-- 指定体の剰余体代数構造と両立する図式なら、極限の同型も元の剰余体上で両立する。 -/
theorem directLimitResidueEquiv_map
    [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
    [IsLocalRing (DirectLimit S f)] [IsLocalHom (algebraMap B (DirectLimit S f))]
    (x : ResidueField B) :
    directLimitResidueEquiv S f g hg hcover
      (ResidueField.map (algebraMap B (DirectLimit S f)) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
  rw [ResidueField.map_residue]
  let i := Classical.arbitrary ι
  rw [← directLimit_algebraMap_comp S f i, RingHom.comp_apply,
    directLimitResidueEquiv_of, (g i).commutes]
  exact IsScalarTower.algebraMap_apply B (ResidueField B) K b

end Residue

/-- 実際の有向図式から、指定体を剰余体に持つ平坦局所拡大を構成する。
添字と段の型がType uなら極限もType u。図式の存在・完備性・Noether性は別課題。 -/
theorem exists_flat_local_extension_of_directed_system
    {B ι K : Type u} [CommRing B] [IsLocalRing B]
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    [Field K] [Algebra (ResidueField B) K] [Algebra B K]
    [IsScalarTower B (ResidueField B) K]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra B (S i)] [∀ i, IsLocalHom (algebraMap B (S i))]
    [∀ i, Module.Flat B (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[B] S j) [DirectedSystem S (f · · ·)]
    (hlocal : ∀ i j h, IsLocalHom (f i j h).toRingHom)
    (hmax : ∀ i, (maximalIdeal B).map (algebraMap B (S i)) = maximalIdeal (S i))
    (g : ∀ i, S i →ₐ[B] K) (hg : ∀ i j h x, g j (f i j h x) = g i x)
    (hcover : ∀ x : K, ∃ i, ∃ y : S i, g i y = x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  let C := DirectLimit S f
  let : IsLocalRing C := directLimit_isLocalRing S f
  let : IsLocalHom (algebraMap B C) := directLimit_algebraMap_isLocalHom S f hlocal
  let : Module.Flat B C := directLimit_flat S f
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    directLimit_maximalIdeal_map S f hlocal hmax, directLimitResidueEquiv S f g hg hcover,
    directLimitResidueEquiv_map S f g hg hcover⟩

end DirectLimit

section IntermediateFieldUnion

variable {B k K : Type*} [CommRing B] [Field k] [Field K]
variable [Algebra B k] [Algebra k K] [Algebra B K] [IsScalarTower B k K]
variable {S : Type*} [CommRing S] [Algebra B S]

section System
variable {ι : Type*} (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable (L : IntermediateField k K) (g : ∀ i, S i →ₐ[B] K)
variable (hmem : ∀ i x, g i x ∈ L)

/-- 指定体への両立する写像は、共通の中間体へ制限しても両立する。 -/
theorem algHom_codRestrict_intermediateField_compatible [Preorder ι]
    (f : ∀ i j, i ≤ j → S i →ₐ[B] S j)
    (hg : ∀ i j h x, g j (f i j h x) = g i x) :
    ∀ i j h x, (g j).codRestrict (L.toSubalgebra.restrictScalars B) (hmem j) (f i j h x) =
      (g i).codRestrict (L.toSubalgebra.restrictScalars B) (hmem i) x := by
  intro i j h x
  apply Subtype.ext
  exact hg i j h x

/-- 各段の像が有向な中間体全体なら、制限した写像の像は合併全体を覆う。 -/
theorem algHom_codRestrict_intermediateField_cover_of_iSup [Nonempty ι]
    (F : ι → IntermediateField k K) (hF : Directed (· ≤ ·) F) (hL : L = ⨆ i, F i)
    (hrange : ∀ i, Set.range (g i) = (F i : Set K)) :
    ∀ x : L, ∃ i, ∃ y : S i,
      (g i).codRestrict (L.toSubalgebra.restrictScalars B) (hmem i) y = x := by
  intro x
  have hx : x.val ∈ (⨆ i, F i : IntermediateField k K) := hL ▸ x.property
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed hF] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [← hrange i] at hi
  obtain ⟨y, hy⟩ := hi
  exact ⟨i, y, Subtype.ext hy⟩

end System

end IntermediateFieldUnion

section GeneratorIndex

/-- 生成元の型そのものを同じ宇宙の整列添字として使用できる。 -/
theorem exists_residueGeneratorOrder (K : Type u) :
    ∃ (_ : LinearOrder K), WellFoundedLT K := exists_wellFoundedLT K

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [LinearOrder K]

/-- 元iを加える前の中間体。 -/
def residueGeneratorBefore (i : K) : IntermediateField k K :=
  IntermediateField.adjoin k (Set.Iio i)

/-- 元iを加えた後の中間体。 -/
def residueGeneratorAfter (i : K) : IntermediateField k K :=
  IntermediateField.adjoin k (Set.Iic i)

/-- 生成元を進めると中間体も増加する。 -/
theorem residueGeneratorAfter_mono : Monotone (residueGeneratorAfter k K) :=
  fun i j hij ↦ IntermediateField.adjoin.mono k (Set.Iic i) (Set.Iic j)
    (Set.Iic_subset_Iic.mpr hij)

/-- 一元を加えることで閉初期部分の中間体が得られる。 -/
theorem residueGeneratorAfter_eq_adjoin (i : K) :
    residueGeneratorAfter k K i =
      (IntermediateField.adjoin (residueGeneratorBefore k K i) {i}).restrictScalars k := by
  rw [residueGeneratorBefore, IntermediateField.adjoin_adjoin_left]
  unfold residueGeneratorAfter
  congr 1
  ext x
  simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
  exact le_iff_lt_or_eq

/-- 開初期部分の中間体は、それ以前の閉初期部分の中間体の合併である。 -/
theorem residueGeneratorBefore_eq_iSup (i : K) :
    residueGeneratorBefore k K i = ⨆ j : Set.Iio i, residueGeneratorAfter k K j.val := by
  have h : (Set.Iio i : Set K) = ⋃ j : Set.Iio i, Set.Iic j.val := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, le_rfl⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact lt_of_le_of_lt hj j.property
  unfold residueGeneratorBefore residueGeneratorAfter
  exact (congrArg (IntermediateField.adjoin k) h).trans
    (IntermediateField.adjoin_iUnion k (fun j : Set.Iio i ↦ Set.Iic j.val))

/-- 最初の生成元の前には、基底体だけがある。 -/
theorem residueGeneratorBefore_eq_bot (i : K) (hi : IsMin i) :
    residueGeneratorBefore k K i = ⊥ := by
  have h : (Set.Iio i : Set K) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
    (fun _ hx ↦ hi.not_lt hx)
  unfold residueGeneratorBefore
  rw [h, IntermediateField.adjoin_empty]

/-- 各指定体の元は、その元までの中間体に入るので、図式はK全体を覆う。 -/
theorem residueGeneratorAfter_cover (x : K) :
    x ∈ residueGeneratorAfter k K x :=
  IntermediateField.subset_adjoin k (Set.Iic x) le_rfl

end GeneratorIndex

section StageMap

open IsLocalRing
variable {B S K : Type*} [CommRing B] [IsLocalRing B]
variable [CommRing S] [IsLocalRing S] [Algebra B S] [IsLocalHom (algebraMap B S)]
variable [Field K] [Algebra (ResidueField B) K] [Algebra B K]
variable [IsScalarTower B (ResidueField B) K]
variable (L : IntermediateField (ResidueField B) K) (e : ResidueField S ≃+* L)
variable (he : ∀ y, e (ResidueField.map (algebraMap B S) y) = algebraMap (ResidueField B) L y)

/-- 剰余体同型を経由して指定体へ送る、基底環上の代数写像。 -/
@[expose] noncomputable def residueFieldStageMap : S →ₐ[B] K where
  __ := L.val.toRingHom.comp (e.toRingHom.comp (residue S))
  commutes' b := by
    change algebraMap L K (e (residue S (algebraMap B S b))) = algebraMap B K b
    rw [← ResidueField.map_residue, he]
    rw [← IsScalarTower.algebraMap_apply (ResidueField B) L K]
    exact (IsScalarTower.algebraMap_apply B (ResidueField B) K b).symm

/-- 段写像の元ごとの計算。 -/
@[simp] theorem residueFieldStageMap_apply (s : S) :
    residueFieldStageMap L e he s = (e (residue S s) : K) := rfl

/-- 段写像の核は、その段の極大イデアル。 -/
theorem residueFieldStageMap_ker :
    RingHom.ker (residueFieldStageMap L e he).toRingHom = maximalIdeal S := by
  ext s
  change (L.val (e (residue S s)) = 0) ↔ s ∈ maximalIdeal S
  rw [← residue_eq_zero_iff]
  constructor
  · intro h
    have h' : L.val (e (residue S s)) = L.val (e 0) := by
      simpa only [map_zero] using h
    exact e.injective (L.val.injective h')
  · intro h
    rw [h, map_zero, map_zero]

/-- 段写像の像は、指定した中間体全体である。 -/
theorem residueFieldStageMap_range :
    Set.range (residueFieldStageMap L e he) = (L : Set K) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact (e (residue S s)).property
  · intro hx
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    obtain ⟨s, hs⟩ := residue_surjective (R := S) y
    refine ⟨s, ?_⟩
    change (e (residue S s) : K) = x
    rw [hs, hy]

section Compatibility
variable {T : Type*} [CommRing T] [IsLocalRing T] [Algebra B T]
variable [IsLocalHom (algebraMap B T)]
variable (M : IntermediateField (ResidueField B) K) (eT : ResidueField T ≃+* M)
variable (heT : ∀ y, eT (ResidueField.map (algebraMap B T) y) = algebraMap (ResidueField B) M y)

/-- 剰余体同型の両立から、段の環から指定体への写像の両立が従う。 -/
theorem residueFieldStageMap_comp
    (f : S →ₐ[B] T) [IsLocalHom f.toRingHom]
    (hres : ∀ y, (eT (ResidueField.map f.toRingHom y) : K) = (e y : K)) :
    (residueFieldStageMap M eT heT).comp f = residueFieldStageMap L e he := by
  ext s
  change (eT (residue T (f.toRingHom s)) : K) = (e (residue S s) : K)
  rw [← ResidueField.map_residue f.toRingHom]
  exact hres (residue S s)

end Compatibility

end StageMap

section BeforeLimit

open IsLocalRing
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]
variable (i : K) (S : {j : K // j < i} → Type u)
variable [∀ j, CommRing (S j)] [∀ j, Algebra B (S j)]
variable (g : ∀ j, S j →ₐ[B] K)
variable (hrange : ∀ j, Set.range (g j) = (residueGeneratorAfter (ResidueField B) K j.val : Set K))

omit [IsScalarTower B (ResidueField B) K] in
include hrange in
/-- 各段の像は開初期部分の生成する中間体に入る。非空性は不要。 -/
theorem beforeLimitStage_mem :
    ∀ j x, g j x ∈ residueGeneratorBefore (ResidueField B) K i := by
  intro j x
  have hle : residueGeneratorAfter (ResidueField B) K j.val ≤
      residueGeneratorBefore (ResidueField B) K i := by
    rw [residueGeneratorBefore_eq_iSup]
    exact le_iSup (fun j : Set.Iio i ↦ residueGeneratorAfter (ResidueField B) K j.val) j
  apply hle
  change g j x ∈ (residueGeneratorAfter (ResidueField B) K j.val : Set K)
  rw [← hrange j]
  exact Set.mem_range_self x

/-- 開初期部分の中間体への、実際の段写像。 -/
@[expose] noncomputable def beforeLimitStageMap (j : {j : K // j < i}) :
    S j →ₐ[B] residueGeneratorBefore (ResidueField B) K i :=
  (g j).codRestrict ((residueGeneratorBefore (ResidueField B) K i).toSubalgebra.restrictScalars B)
    (beforeLimitStage_mem i S g hrange j)

@[simp] theorem beforeLimitStageMap_coe (j : {j : K // j < i}) (x : S j) :
    (beforeLimitStageMap i S g hrange j x : K) = g j x := rfl

include hrange in
/-- After jの単調性と合併から、制限した段写像はBefore i全体を覆う。 -/
theorem beforeLimitStageMap_cover [Nonempty {j : K // j < i}] :
    ∀ x : residueGeneratorBefore (ResidueField B) K i,
      ∃ j, ∃ y : S j, beforeLimitStageMap i S g hrange j y = x := by
  have hmono : Monotone (fun j : {j : K // j < i} ↦
      residueGeneratorAfter (ResidueField B) K j.val) :=
    fun _ _ h ↦ residueGeneratorAfter_mono (ResidueField B) K h
  exact algHom_codRestrict_intermediateField_cover_of_iSup S
    (residueGeneratorBefore (ResidueField B) K i) g (beforeLimitStage_mem i S g hrange)
    (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val) hmono.directed_le
    (residueGeneratorBefore_eq_iSup (ResidueField B) K i) hrange

variable (f : ∀ j k, j ≤ k → S j →ₐ[B] S k)
variable (hg : ∀ j k h x, g k (f j k h x) = g j x)

include hg in
/-- Kへの両立する段写像をBefore iへ制限した後も両立する。 -/
theorem beforeLimitStageMap_compatible :
    ∀ j k h x, beforeLimitStageMap i S g hrange k (f j k h x) =
      beforeLimitStageMap i S g hrange j x :=
  algHom_codRestrict_intermediateField_compatible _ _ _ _ f hg

variable [Nonempty {j : K // j < i}] [DirectedSystem S (f · · ·)]

/-- 構成済みの開初期部分の図式の直極限の剰余体をBefore iへ同定する。 -/
noncomputable def residueFieldBeforeLimitEquiv [IsLocalRing (DirectLimit S f)] :
    ResidueField (DirectLimit S f) ≃+* residueGeneratorBefore (ResidueField B) K i :=
  directLimitResidueEquiv S f (beforeLimitStageMap i S g hrange)
    (beforeLimitStageMap_compatible i S g hrange f hg) (beforeLimitStageMap_cover i S g hrange)

/-- 極限の剰余体同型は、各段の指定体への写像と一致する。 -/
@[simp] theorem residueFieldBeforeLimitEquiv_of [IsLocalRing (DirectLimit S f)]
    (j : {j : K // j < i}) (x : S j) :
    (residueFieldBeforeLimitEquiv i S g hrange f hg
      (residue (DirectLimit S f) (DirectLimit.Ring.of S f j x)) : K) = g j x := by
  rw [residueFieldBeforeLimitEquiv, directLimitResidueEquiv_of, beforeLimitStageMap_coe]

/-- 極限の剰余体同型は、元の剰余体の係数写像と両立する。 -/
theorem residueFieldBeforeLimitEquiv_map [IsLocalRing (DirectLimit S f)]
    [IsLocalHom (algebraMap B (DirectLimit S f))] (x : ResidueField B) :
    residueFieldBeforeLimitEquiv i S g hrange f hg
      (ResidueField.map (algebraMap B (DirectLimit S f)) x) =
        algebraMap (ResidueField B) (residueGeneratorBefore (ResidueField B) K i) x :=
  directLimitResidueEquiv_map S f (beforeLimitStageMap i S g hrange)
    (beforeLimitStageMap_compatible i S g hrange f hg) (beforeLimitStageMap_cover i S g hrange) x

/-- 開初期部分の極限に生成元iを加え、After iを剰余体とする次の環を構成する。
極限の局所性・平坦性・極大イデアル等式を保存定理で供給し、後続段を実際に適用する。 -/
theorem exists_residueField_successor_of_beforeLimit
    [∀ j, IsLocalRing (S j)] [∀ j, IsLocalHom (algebraMap B (S j))]
    [∀ j, Module.Flat B (S j)]
    (hlocal : ∀ j k h, IsLocalHom (f j k h).toRingHom)
    (hmax : ∀ j, (maximalIdeal B).map (algebraMap B (S j)) = maximalIdeal (S j)) :
    letI : IsLocalRing (DirectLimit S f) := directLimit_isLocalRing S f
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T)
      (_ : Algebra (DirectLimit S f) T) (_ : Algebra B T)
      (_ : IsScalarTower B (DirectLimit S f) T)
      (_ : IsLocalHom (algebraMap (DirectLimit S f) T)) (_ : IsLocalHom (algebraMap B T)),
      Module.Flat (DirectLimit S f) T ∧ Module.Flat B T ∧
      (maximalIdeal (DirectLimit S f)).map (algebraMap (DirectLimit S f) T) = maximalIdeal T ∧
      (maximalIdeal B).map (algebraMap B T) = maximalIdeal T ∧
      ∃ eT : ResidueField T ≃+* residueGeneratorAfter (ResidueField B) K i,
        (∀ y, eT (ResidueField.map (algebraMap B T) y) =
          algebraMap (ResidueField B) (residueGeneratorAfter (ResidueField B) K i) y) ∧
        (∀ y, (eT (ResidueField.map (algebraMap (DirectLimit S f) T) y) : K) =
          (residueFieldBeforeLimitEquiv i S g hrange f hg y : K)) ∧
        ∃ t : T, (eT (residue T t) : K) = i := by
  let D := DirectLimit S f
  let : IsLocalRing D := directLimit_isLocalRing S f
  let : IsLocalHom (algebraMap B D) := directLimit_algebraMap_isLocalHom S f hlocal
  let : Module.Flat B D := directLimit_flat S f
  have hDmax := directLimit_maximalIdeal_map S f hlocal hmax
  let L := residueGeneratorBefore (ResidueField B) K i
  let E := IntermediateField.adjoin L {i}
  let eD := residueFieldBeforeLimitEquiv i S g hrange f hg
  have heD := residueFieldBeforeLimitEquiv_map i S g hrange f hg
  obtain ⟨T, tRing, tLocal, tAlgD, tAlgB, tTower, tHomD, tHomB,
    tFlatD, tFlatB, tNoeth, htDmax, htBmax, eE, heE, heStep, t, ht⟩ :=
    exists_residueField_successor B D K L eD heD hDmax i
  let v : E ≃ₐ[ResidueField B] residueGeneratorAfter (ResidueField B) K i :=
    IntermediateField.equivOfEq (residueGeneratorAfter_eq_adjoin (ResidueField B) K i).symm
  have hv (x : E) : (v x : K) = (x : K) := by
    with_unfolding_all rfl
  refine ⟨T, tRing, tLocal, tAlgD, tAlgB, tTower, tHomD, tHomB,
    tFlatD, tFlatB, htDmax, htBmax, eE.trans v.toRingEquiv, ?_, ?_, t, ?_⟩
  · intro y
    change v (eE (ResidueField.map (algebraMap B T) y)) = _
    rw [heE]
    exact v.commutes y
  · intro y
    change (v (eE (ResidueField.map (algebraMap D T) y)) : K) = _
    rw [hv, heStep]
    rfl
  · change (v (eE (residue T t)) : K) = i
    rw [hv, ht]
    rfl

end BeforeLimit

end SerrePositivity

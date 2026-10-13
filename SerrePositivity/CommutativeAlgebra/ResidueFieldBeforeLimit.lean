module

public import SerrePositivity.CommutativeAlgebra.IntermediateFieldUnionMap
public import SerrePositivity.CommutativeAlgebra.ResidueFieldGeneratorIndex
public import SerrePositivity.CommutativeAlgebra.ResidueFieldDirectLimit
public import SerrePositivity.CommutativeAlgebra.ResidueFieldSuccessor

/-! # 開初期部分の極限の指定剰余体

各段の指定体への像がAfter jなら、その両立する図式の直極限の剰余体はBefore iである。
体全体への被覆を仮定せず、初期部分の合併からBefore iへの被覆を証明する。
空の初期部分は基底環を使う別の段階であり、極限の入口は非空の場合を扱う。
-/

public section
namespace SerrePositivity
open IsLocalRing
universe u
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
  algHomToIntermediateField _ (g j) (beforeLimitStage_mem i S g hrange j)

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
  exact algHomToIntermediateField_cover_of_iSup S
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
  algHomToIntermediateField_compatible _ _ _ _ f hg

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

end SerrePositivity

module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.AlgebraSystem
public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.Limit

/-! # 閉初期部分の延長の一段

## 概要

生成元の添字 `i` について、`i` 未満の段の図式（開初期部分）から `i` までの図式（閉初期部分）を作る。
`i` が最小元なら基底環 `B` から、そうでなければ開初期部分の直極限から、生成元 `i` を一つ加える
（`exists_residueField_closed_extension`）。検証済みの延長を選ぶ関数が `residueFieldClosedStep`。

## 方針

最小元の場合（`ResidueFieldMinExtension`）と極限の後の場合（`ResidueFieldBeforeExtension`）を、
`ResidueFieldExtension/AlgebraSystem` の終段の追加で同じ形の閉初期部分の図式にまとめる。
延長の法則（平坦性・局所性・`m_B` の拡張・剰余体）は `IsResidueFieldClosedExtension` にまとめて保持する。

## 規約

全段で一致する履歴の再帰構成はこの一段とは別（`ResidueFieldExtension/Glue`）。

## 使われ方

図式としての延長と貼り合わせ（`ResidueFieldExtension/Glue`）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section ClosedExtension

open IsLocalRing
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]

/-- 閉初期部分の延長の法則。候補の環と写像に対する性質であり、存在定理ではない。 -/
def IsResidueFieldClosedExtension
    (i : K) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
    (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) (g : ∀ j, S j →ₐ[B] K)
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra B T]
    (c : ∀ j, S j →ₐ[B] T) (gT : T →ₐ[B] K) : Prop :=
  Module.Flat B T ∧ (maximalIdeal B).map (algebraMap B T) = maximalIdeal T ∧
  Set.range gT = (residueGeneratorAfter (ResidueField B) K i : Set K) ∧
  RingHom.ker gT.toRingHom = maximalIdeal T ∧ (∃ t : T, gT t = i) ∧
  (∀ j k h x, c k (f j k h x) = c j x) ∧ (∀ j x, gT (c j x) = g j x) ∧
  (∀ j, IsLocalHom (c j).toRingHom) ∧
  DirectedSystem (algebraInitialSegmentObj i S T) (algebraInitialSegmentMap i S T f c · · ·) ∧
  (∀ j k h, IsLocalHom (algebraInitialSegmentMap i S T f c j k h).toRingHom) ∧
  (∀ j k h x, algebraInitialSegmentTarget i S T g gT k
    (algebraInitialSegmentMap i S T f c j k h x) =
      algebraInitialSegmentTarget i S T g gT j x) ∧
  (∀ j, Module.Flat B (algebraInitialSegmentObj i S T j)) ∧
  (∀ j, (maximalIdeal B).map (algebraMap B (algebraInitialSegmentObj i S T j)) =
    maximalIdeal (algebraInitialSegmentObj i S T j)) ∧
  (∀ j, Set.range (algebraInitialSegmentTarget i S T g gT j) =
    (residueGeneratorAfter (ResidueField B) K j.val : Set K))

omit [IsScalarTower B (ResidueField B) K] in
/-- 両立する局所なcoconeと新終段の代数的な評価から、閉延長の全法則を導く。
初期部分の図式の法則・全段の像・平坦性は既存の延長APIを適用して確認する。 -/
theorem isResidueFieldClosedExtension_of_cocone
    (i : K) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
    [∀ j, Module.Flat B (S j)]
    (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) [DirectedSystem S (f · · ·)]
    (g : ∀ j, S j →ₐ[B] K)
    (hrange : ∀ j, Set.range (g j) = (residueGeneratorAfter (ResidueField B) K j.val : Set K))
    (hg : ∀ j k h x, g k (f j k h x) = g j x)
    (hlocal : ∀ j k h, IsLocalHom (f j k h).toRingHom)
    (hmax : ∀ j, (maximalIdeal B).map (algebraMap B (S j)) = maximalIdeal (S j))
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra B T] [Module.Flat B T]
    (c : ∀ j, S j →ₐ[B] T) (gT : T →ₐ[B] K)
    (htmax : (maximalIdeal B).map (algebraMap B T) = maximalIdeal T)
    (htRange : Set.range gT = (residueGeneratorAfter (ResidueField B) K i : Set K))
    (htKer : RingHom.ker gT.toRingHom = maximalIdeal T) (htGen : ∃ t : T, gT t = i)
    (hc : ∀ j k h x, c k (f j k h x) = c j x)
    (hgc : ∀ j x, gT (c j x) = g j x)
    (hcLocal : ∀ j, IsLocalHom (c j).toRingHom) :
    IsResidueFieldClosedExtension i S f g T c gT := by
  refine ⟨inferInstance, htmax, htRange, htKer, htGen, hc, hgc, hcLocal,
    algebraInitialSegment_directedSystem i S T f c hc,
    algebraInitialSegmentMap_isLocalHom i S T f c hlocal hcLocal,
    algebraInitialSegmentTarget_compatible i S T f c g gT hg hgc,
    ?_, algebraInitialSegment_maximalIdeal_map i S T hmax htmax, ?_⟩
  · intro j
    infer_instance
  · intro j
    by_cases hj : j.val = i
    · have heq : j = ⟨i, le_rfl⟩ := Subtype.ext hj
      rw [heq, algebraInitialSegmentTarget_range_last]
      exact htRange
    · have hjlt : j.val < i := lt_of_le_of_ne j.property hj
      rw [show j = ⟨j.val, hjlt.le⟩ from rfl,
        algebraInitialSegmentTarget_range_old i S T g gT ⟨j.val, hjlt⟩]
      exact hrange ⟨j.val, hjlt⟩

end ClosedExtension

section MinExtension

open IsLocalRing
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]

/-- 最小元の前の中間体を、基底の剰余体そのものへ同定する。 -/
noncomputable def residueFieldMinEquiv (i : K) (hi : IsMin i) :
    ResidueField B ≃ₐ[ResidueField B] residueGeneratorBefore (ResidueField B) K i :=
  (IntermediateField.botEquiv (ResidueField B) K).symm.trans
    (IntermediateField.equivOfEq (residueGeneratorBefore_eq_bot (ResidueField B) K i hi).symm)

/-- 最小元の初期段を、生成元を加えた閉初期部分の図式へ延長する。
Noether性は不要。旧段への写像・図式の条件は空添字から実際に供給する。 -/
theorem exists_closed_extension_of_min
    (i : K) (hi : IsMin i) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
    (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) (g : ∀ j, S j →ₐ[B] K) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T) (_ : Algebra B T)
      (_ : IsLocalHom (algebraMap B T)),
      ∃ (c : ∀ j, S j →ₐ[B] T) (gT : T →ₐ[B] K),
        IsResidueFieldClosedExtension i S f g T c gT := by
  let L := residueGeneratorBefore (ResidueField B) K i
  let E := IntermediateField.adjoin L {i}
  let eB := residueFieldMinEquiv (B := B) i hi
  have heB (y : ResidueField B) :
      eB.toRingEquiv (ResidueField.map (algebraMap B B) y) = algebraMap (ResidueField B) L y := by
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) y
    rw [ResidueField.map_residue]
    exact eB.commutes (residue B b)
  obtain ⟨T, tRing, tLocal, tAlgOld, tAlgB, tTower, tHomOld, tHomB,
    tFlatOld, tFlatB, tNoeth, htOldMax, htBmax, eE, heE, heStep, t, ht⟩ :=
    exists_residueField_successor B B K L eB.toRingEquiv heB (by simp) i
  let : Module.Flat B T := tFlatB
  let v : E ≃ₐ[ResidueField B] residueGeneratorAfter (ResidueField B) K i :=
    IntermediateField.equivOfEq (residueGeneratorAfter_eq_adjoin (ResidueField B) K i).symm
  let eT : ResidueField T ≃+* residueGeneratorAfter (ResidueField B) K i :=
    eE.trans v.toRingEquiv
  have heT (y : ResidueField B) :
      eT (ResidueField.map (algebraMap B T) y) =
        algebraMap (ResidueField B) (residueGeneratorAfter (ResidueField B) K i) y := by
    change v (eE (ResidueField.map (algebraMap B T) y)) = _
    rw [heE]
    exact v.commutes y
  have ht' : (eT (residue T t) : K) = i := by
    change (v (eE (residue T t)) : K) = i
    rw [ht]
    with_unfolding_all rfl
  let G : T →ₐ[B] K := residueFieldStageMap
    (residueGeneratorAfter (ResidueField B) K i) eT heT
  let c : ∀ j, S j →ₐ[B] T := fun j ↦ False.elim (hi.not_lt j.property)
  let : ∀ j, Module.Flat B (S j) := fun j ↦ False.elim (hi.not_lt j.property)
  let : DirectedSystem S (f · · ·) := by
    constructor
    · intro j x
      exact False.elim (hi.not_lt j.property)
    · intro l k j hjk hkl x
      exact False.elim (hi.not_lt j.property)
  refine ⟨T, tRing, tLocal, tAlgB, tHomB, c, G, ?_⟩
  apply isResidueFieldClosedExtension_of_cocone i S f g
    (fun j ↦ False.elim (hi.not_lt j.property))
    (fun j k h x ↦ False.elim (hi.not_lt j.property))
    (fun j k h ↦ False.elim (hi.not_lt j.property))
    (fun j ↦ False.elim (hi.not_lt j.property)) T c G htBmax
    (residueFieldStageMap_range _ eT heT) (residueFieldStageMap_ker _ eT heT) ⟨t, ht'⟩
    (fun j k h x ↦ False.elim (hi.not_lt j.property))
    (fun j x ↦ False.elim (hi.not_lt j.property))
    (fun j ↦ False.elim (hi.not_lt j.property))

end MinExtension

section BeforeExtension

open IsLocalRing
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]

/-- 非空の開初期部分の図式を、生成元iを加えた閉初期部分の図式へ実際に延長する。
新終段への両立・局所性・平坦性・極大イデアル・全段の指定体への像を構成中に確認する。 -/
theorem exists_closed_extension_of_beforeLimit
    (i : K) [Nonempty {j : K // j < i}]
    (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
    [∀ j, IsLocalHom (algebraMap B (S j))] [∀ j, Module.Flat B (S j)]
    (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) [DirectedSystem S (f · · ·)]
    (g : ∀ j, S j →ₐ[B] K)
    (hrange : ∀ j, Set.range (g j) = (residueGeneratorAfter (ResidueField B) K j.val : Set K))
    (hg : ∀ j k h x, g k (f j k h x) = g j x)
    (hlocal : ∀ j k h, IsLocalHom (f j k h).toRingHom)
    (hmax : ∀ j, (maximalIdeal B).map (algebraMap B (S j)) = maximalIdeal (S j)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T) (_ : Algebra B T)
      (_ : IsLocalHom (algebraMap B T)),
      ∃ (c : ∀ j, S j →ₐ[B] T) (gT : T →ₐ[B] K),
        Module.Flat B T ∧ (maximalIdeal B).map (algebraMap B T) = maximalIdeal T ∧
        Set.range gT = (residueGeneratorAfter (ResidueField B) K i : Set K) ∧
        RingHom.ker gT.toRingHom = maximalIdeal T ∧ (∃ t : T, gT t = i) ∧
        (∀ j k h x, c k (f j k h x) = c j x) ∧ (∀ j x, gT (c j x) = g j x) ∧
        DirectedSystem (algebraInitialSegmentObj i S T) (algebraInitialSegmentMap i S T f c · · ·) ∧
        (∀ j k h, IsLocalHom (algebraInitialSegmentMap i S T f c j k h).toRingHom) ∧
        (∀ j k h x, algebraInitialSegmentTarget i S T g gT k
          (algebraInitialSegmentMap i S T f c j k h x) =
            algebraInitialSegmentTarget i S T g gT j x) ∧
        (∀ j, Module.Flat B (algebraInitialSegmentObj i S T j)) ∧
        (∀ j, (maximalIdeal B).map (algebraMap B (algebraInitialSegmentObj i S T j)) =
          maximalIdeal (algebraInitialSegmentObj i S T j)) ∧
        (∀ j, Set.range (algebraInitialSegmentTarget i S T g gT j) =
          (residueGeneratorAfter (ResidueField B) K j.val : Set K)) := by
  let D := DirectLimit S f
  let : IsLocalRing D := directLimit_isLocalRing S f
  obtain ⟨T, tRing, tLocal, tAlgD, tAlgB, tTower, tHomD, tHomB,
    tFlatD, tFlatB, htDmax, htBmax, eT, heT, heStep, t, ht⟩ :=
    exists_residueField_successor_of_beforeLimit i S g hrange f hg hlocal hmax
  let : Module.Flat B T := tFlatB
  let q : D →ₐ[B] T := IsScalarTower.toAlgHom B D T
  let : IsLocalHom q.toRingHom := by
    change IsLocalHom (algebraMap D T)
    infer_instance
  let G : T →ₐ[B] K := residueFieldStageMap
    (residueGeneratorAfter (ResidueField B) K i) eT heT
  have hq : G.comp q = DirectLimit.Algebra.lift S f K g hg := by
    apply DirectLimit.Algebra.hom_ext (G := S) (f := f)
    intro j
    ext x
    change (eT (residue T (algebraMap D T (DirectLimit.Ring.of S f j x))) : K) = g j x
    rw [← ResidueField.map_residue, heStep]
    exact residueFieldBeforeLimitEquiv_of i S g hrange f hg j x
  let c : ∀ j, S j →ₐ[B] T := fun j ↦ q.comp (DirectLimit.Algebra.of S f j)
  have hc : ∀ j k h x, c k (f j k h x) = c j x := by
    intro j k h x
    exact congrArg q (DirectLimit.Algebra.of_f (G := S) (f := f) h x)
  have hgc : ∀ j x, G (c j x) = g j x := by
    intro j x
    change (G.comp q) (DirectLimit.Algebra.of S f j x) = g j x
    rw [hq, DirectLimit.Algebra.lift_of]
  have hcLocal (j : {j : K // j < i}) : IsLocalHom (c j).toRingHom := by
    let : IsLocalHom (DirectLimit.Algebra.of S f j).toRingHom := directLimit_isLocalHom S f hlocal j
    change IsLocalHom (q.toRingHom.comp (DirectLimit.Algebra.of S f j).toRingHom)
    infer_instance
  have hG := residueFieldStageMap_range (residueGeneratorAfter (ResidueField B) K i) eT heT
  refine ⟨T, tRing, tLocal, tAlgB, tHomB, c, G, tFlatB, htBmax, hG,
    residueFieldStageMap_ker _ eT heT, ⟨t, ht⟩, hc, hgc,
    algebraInitialSegment_directedSystem i S T f c hc,
    algebraInitialSegmentMap_isLocalHom i S T f c hlocal hcLocal,
    algebraInitialSegmentTarget_compatible i S T f c g G hg hgc,
    ?_, algebraInitialSegment_maximalIdeal_map i S T hmax htBmax, ?_⟩
  · intro j
    infer_instance
  · intro j
    by_cases hj : j.val = i
    · have heq : j = ⟨i, le_rfl⟩ := Subtype.ext hj
      rw [heq, algebraInitialSegmentTarget_range_last]
      exact hG
    · have hjlt : j.val < i := lt_of_le_of_ne j.property hj
      rw [show j = ⟨j.val, hjlt.le⟩ from rfl,
        algebraInitialSegmentTarget_range_old i S T g G ⟨j.val, hjlt⟩]
      exact hrange ⟨j.val, hjlt⟩

end BeforeExtension

section ClosedStep

open IsLocalRing
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]

/-- 開初期部分の空・非空にかかわらず、同じ法則を満たす閉延長を構成する。 -/
theorem exists_residueField_closed_extension
    (i : K) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
    [∀ j, IsLocalHom (algebraMap B (S j))] [∀ j, Module.Flat B (S j)]
    (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) [DirectedSystem S (f · · ·)]
    (g : ∀ j, S j →ₐ[B] K)
    (hrange : ∀ j, Set.range (g j) = (residueGeneratorAfter (ResidueField B) K j.val : Set K))
    (hg : ∀ j k h x, g k (f j k h x) = g j x)
    (hlocal : ∀ j k h, IsLocalHom (f j k h).toRingHom)
    (hmax : ∀ j, (maximalIdeal B).map (algebraMap B (S j)) = maximalIdeal (S j)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T) (_ : Algebra B T)
      (_ : IsLocalHom (algebraMap B T)),
      ∃ (c : ∀ j, S j →ₐ[B] T) (gT : T →ₐ[B] K),
        IsResidueFieldClosedExtension i S f g T c gT := by
  classical
  by_cases h : Nonempty {j : K // j < i}
  · let := h
    obtain ⟨T, tRing, tLocal, tAlg, tHom, c, gT,
      hflat, htmax, htrange, htker, htgen, hc, hgc, hds, hclosedLocal,
      htarget, hclosedFlat, hclosedMax, hclosedRange⟩ :=
      exists_closed_extension_of_beforeLimit i S f g hrange hg hlocal hmax
    have hcLocal (j : {j : K // j < i}) : IsLocalHom (c j).toRingHom := by
      apply ((local_hom_TFAE (c j).toRingHom).out 1 3).mpr
      rw [← hmax j, Ideal.map_map]
      have hcomp : (c j).toRingHom.comp (algebraMap B (S j)) = algebraMap B T := by
        ext b
        exact (c j).commutes b
      rw [hcomp, htmax]
    exact ⟨T, tRing, tLocal, tAlg, tHom, c, gT,
      hflat, htmax, htrange, htker, htgen, hc, hgc, hcLocal,
      hds, hclosedLocal, htarget, hclosedFlat, hclosedMax, hclosedRange⟩
  · have hi : IsMin i := by
      refine isMin_iff_forall_not_lt.mpr ?_
      intro j hj
      exact h ⟨⟨j, hj⟩⟩
    exact exists_closed_extension_of_min i hi S f g

/-- 延長の対象と写像。平坦性・像・図式の両立は別の述語で検証する。 -/
structure ResidueFieldClosedStepData
    (i : K) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, Algebra B (S j)] where
  carrier : Type u
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [algebra : Algebra B carrier]
  [baseLocal : IsLocalHom (algebraMap B carrier)]
  incoming : ∀ j, S j →ₐ[B] carrier
  target : carrier →ₐ[B] K

attribute [instance] ResidueFieldClosedStepData.commRing ResidueFieldClosedStepData.localRing
  ResidueFieldClosedStepData.algebra ResidueFieldClosedStepData.baseLocal

variable (i : K) (S : {j : K // j < i} → Type u)
variable [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
variable [∀ j, IsLocalHom (algebraMap B (S j))] [∀ j, Module.Flat B (S j)]
variable (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) [DirectedSystem S (f · · ·)]
variable (g : ∀ j, S j →ₐ[B] K)
variable (hrange : ∀ j, Set.range (g j) = (residueGeneratorAfter (ResidueField B) K j.val : Set K))
variable (hg : ∀ j k h x, g k (f j k h x) = g j x)
variable (hlocal : ∀ j k h, IsLocalHom (f j k h).toRingHom)
variable (hmax : ∀ j, (maximalIdeal B).map (algebraMap B (S j)) = maximalIdeal (S j))

include hrange hg hlocal hmax

/-- 候補の存在と検証を、対象を格納する型に移す。 -/
theorem exists_lawful_residueFieldClosedStepData :
    ∃ d : ResidueFieldClosedStepData (B := B) i S,
      IsResidueFieldClosedExtension i S f g d.carrier d.incoming d.target := by
  obtain ⟨T, tRing, tLocal, tAlg, tHom, c, gT, h⟩ :=
    exists_residueField_closed_extension i S f g hrange hg hlocal hmax
  exact ⟨{
    carrier := T
    commRing := tRing
    localRing := tLocal
    algebra := tAlg
    baseLocal := tHom
    incoming := c
    target := gT }, h⟩

/-- 同じ入力には同じ候補を返す一段延長。法則は下の定理で保証する。 -/
noncomputable def residueFieldClosedStep : ResidueFieldClosedStepData (B := B) i S :=
  Classical.choose (exists_lawful_residueFieldClosedStepData i S f g hrange hg hlocal hmax)

/-- 選んだ対象と写像は、構成した閉延長の全法則を満たす。 -/
theorem residueFieldClosedStep_spec :
    let d := residueFieldClosedStep i S f g hrange hg hlocal hmax
    IsResidueFieldClosedExtension i S f g d.carrier d.incoming d.target :=
  Classical.choose_spec (exists_lawful_residueFieldClosedStepData i S f g hrange hg hlocal hmax)

end ClosedStep

end SerrePositivity

module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldBeforeLimit
public import SerrePositivity.CommutativeAlgebra.ResidueFieldStageMap
public import SerrePositivity.CommutativeAlgebra.AlgebraInitialSegment

/-! # 開初期部分の極限から閉初期部分の図式へ

Before iを剰余体に持つ直極限に一元を加え、After iを剰余体に持つ新終段を構成する。
旧段からの写像とKへの写像を実際に作り、閉初期部分の図式の法則・像・不変条件を確認する。
各初期部分の履歴を全段で両立して選ぶ再帰自体は、この一段延長とは別の課題。
-/

public section
namespace SerrePositivity
open IsLocalRing
universe u
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

end SerrePositivity

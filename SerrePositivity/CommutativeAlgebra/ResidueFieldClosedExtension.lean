module

public import SerrePositivity.CommutativeAlgebra.AlgebraInitialSegment
public import SerrePositivity.CommutativeAlgebra.ResidueFieldGeneratorIndex

/-! # 構成した閉初期部分の延長の法則

具体的な新終段T、旧段からの写像c、指定体への写像gTに対する述語。
空・非空の二つの構成が、同じ法則を満たすことを証明してから選択する。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
universe u
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

end SerrePositivity

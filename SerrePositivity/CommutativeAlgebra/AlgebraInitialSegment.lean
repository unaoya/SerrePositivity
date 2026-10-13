module

public import SerrePositivity.CommutativeAlgebra.InitialSegmentWithTop
public import SerrePositivity.CommutativeAlgebra.AlgebraSystemReindex
public import SerrePositivity.CommutativeAlgebra.AlgebraSystemWithTop
public import SerrePositivity.CommutativeAlgebra.DirectLimitLocalRing

/-! # 開初期部分の代数図式に終段を加える

WithTopによる延長を、閉初期部分Iic iへ具体的に移す。
旧段の環と遷移写像を保持し、有向図式の法則・局所性・指定終域への両立を供給する。
-/

@[expose] public section
namespace SerrePositivity
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

/-- 旧段から終段への写像も、添字変更前のcと一致する。 -/
theorem algebraInitialSegmentMap_last (j : {j : ι // j < i}) :
    HEq (algebraInitialSegmentMap i S T f c ⟨j.val, j.property.le⟩ ⟨i, le_rfl⟩ j.property.le)
      (c j) := by
  exact algebraSystemMap_heq_of_eq (algebraSystemWithTopObj S T)
    (algebraSystemWithTopMap S T f c)
    (initialSegmentWithTopEquiv_symm_coe i j) (initialSegmentWithTopEquiv_symm_top i)
    ((initialSegmentWithTopEquiv i).symm.monotone j.property.le) le_top

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

/-- 開初期部分の直極限から次の環への写像で、閉初期部分の図式を作る。 -/
theorem algebraInitialSegment_of_directLimit
    [Nonempty {j : ι // j < i}] [DirectedSystem S (f · · ·)]
    (q : DirectLimit S f →ₐ[B] T) :
    DirectedSystem (algebraInitialSegmentObj i S T)
      (algebraInitialSegmentMap i S T f
        (fun j ↦ q.comp (DirectLimit.Algebra.of S f j)) · · ·) := by
  apply algebraInitialSegment_directedSystem
  intro j k h x
  simp only [AlgHom.comp_apply, DirectLimit.Algebra.of_f]

/-- 開初期部分の極限からの写像が局所なら、閉初期部分の新しい遷移も局所。 -/
theorem algebraInitialSegment_of_directLimit_isLocalHom
    [Nonempty {j : ι // j < i}] [DirectedSystem S (f · · ·)]
    (q : DirectLimit S f →ₐ[B] T) [IsLocalHom q.toRingHom]
    (hf : ∀ j k h, IsLocalHom (f j k h).toRingHom) :
    ∀ j k h, IsLocalHom (algebraInitialSegmentMap i S T f
      (fun j ↦ q.comp (DirectLimit.Algebra.of S f j)) j k h).toRingHom := by
  apply algebraInitialSegmentMap_isLocalHom
  · exact hf
  · intro j
    let : IsLocalHom (DirectLimit.Algebra.of S f j).toRingHom := directLimit_isLocalHom S f hf j
    change IsLocalHom (q.toRingHom.comp (DirectLimit.Algebra.of S f j).toRingHom)
    infer_instance

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

/-- 新しい終段の指定終域への写像はgTである。 -/
theorem algebraInitialSegmentTarget_last :
    HEq (algebraInitialSegmentTarget i S T g gT ⟨i, le_rfl⟩) gT := by
  exact algebraSystemTarget_heq_of_eq (algebraSystemWithTopObj S T)
    (algebraSystemWithTopTarget S T g gT) (initialSegmentWithTopEquiv_symm_top i)

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

/-- 指定終域への写像と両立する極限からの写像で、閉初期部分の両立を供給する。 -/
theorem algebraInitialSegmentTarget_of_directLimit
    [Nonempty {j : ι // j < i}] [DirectedSystem S (f · · ·)]
    (hg : ∀ j k h x, g k (f j k h x) = g j x)
    (q : DirectLimit S f →ₐ[B] T)
    (hq : gT.comp q = DirectLimit.Algebra.lift S f K g hg) :
    ∀ j k h x, algebraInitialSegmentTarget i S T g gT k
      (algebraInitialSegmentMap i S T f
        (fun j ↦ q.comp (DirectLimit.Algebra.of S f j)) j k h x) =
        algebraInitialSegmentTarget i S T g gT j x := by
  apply algebraInitialSegmentTarget_compatible
  · exact hg
  · intro j x
    change (gT.comp q) (DirectLimit.Algebra.of S f j x) = g j x
    rw [hq, DirectLimit.Algebra.lift_of]

end Target
end SerrePositivity

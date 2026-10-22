module
public import SerrePositivity.KST.SConstruction.DGEndInclusionPerfectFull
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfGeneration

/-! # 元の指定 End 包含の実 Perf 延長の生成性
概要：同じ指定代表が Perf を生成すれば、元の End 包含の実 Perf 延長は本質的全射。
方針：D の既存本質像 retract 閉性と、元の代表への延長比較を使う。
規約：生成条件は明示入力。使われ方：同じ対角商の元の End 包含の Morita 性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (b : D)
local notation "F" => endomorphismInclusion R b
local notation "T" => quasiEquivalencePerfectExtension R (EndomorphismObject b) D (F)
local notation "I" => perfectModuleInclusion R D Set.univ
local instance : (I).Full := inferInstanceAs ((modulePerfect R D).ι.Full)
local instance : (I).Faithful := inferInstanceAs ((modulePerfect R D).ι.Faithful)
local instance : (T).CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift R (EndomorphismObject b) D (F)
local instance : (T).IsTriangulated :=
  quasiEquivalencePerfectExtensionIsTriangulated R (EndomorphismObject b) D (F)

/-- 同じ指定代表の生成条件から、元の End 包含の実 Perf 延長は本質的全射。 -/
lemma dgEndInclusionPerfect_essSurj
    (hgen : modulePerfectOver R D {b} = modulePerfect R D) : (T).EssSurj := by
  let h := dgEndInclusionPerfectFullyFaithful R D b
  let : (T).Full := h.full
  let : (T).Faithful := h.faithful
  let J := (T) ⋙ (I)
  let : J.essImage.IsStableUnderRetracts := Morita.criterionPerfEssImage_retract_closed J
  have hall : modulePerfect R D ≤ J.essImage := by
    rw [← hgen]
    apply modulePerfectOver_le_of_generators R D J.essImage
    intro y hy
    have hy : y = b := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨⟨_, modulePerfectOver_representable R (EndomorphismObject b)
      EndomorphismObject.point (Set.mem_univ _)⟩,
      ⟨dgDerivedExtensionRepresentableIso R (EndomorphismObject b) D (F)
        EndomorphismObject.point⟩⟩
  refine ⟨fun Y => ?_⟩
  obtain ⟨X, ⟨e⟩⟩ := hall Y.obj Y.property
  exact ⟨X, ⟨(I).preimageIso e⟩⟩

/-- 同じ指定代表が生成すると、元の End 包含に沿う実 Perf 延長そのものが圏同値。 -/
lemma dgEndInclusionPerfect_isEquivalence
    (hgen : modulePerfectOver R D {b} = modulePerfect R D) : (T).IsEquivalence := by
  let h := dgEndInclusionPerfectFullyFaithful R D b
  let : (T).Full := h.full
  let : (T).Faithful := h.faithful
  let : (T).EssSurj := dgEndInclusionPerfect_essSurj R D b hgen
  exact {}

/-- 順方向を元の End 包含の実 Perf 延長とする、同じ生成条件下の圏同値。 -/
def dgEndInclusionPerfectEquivalence
    (hgen : modulePerfectOver R D {b} = modulePerfect R D) :
    PerfectModuleCategory R (EndomorphismObject b) ≌ PerfectModuleCategory R D := by
  let : (T).IsEquivalence := dgEndInclusionPerfect_isEquivalence R D b hgen
  exact (T).asEquivalence

end SerrePositivity.KST.SConstruction

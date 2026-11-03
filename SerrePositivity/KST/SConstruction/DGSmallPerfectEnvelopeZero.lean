module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeEquivalence
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 元の零加群を保持する小さい Perf 模型の閉零対象
概要：指定小模型の零対象は、元の実零加群そのものとして選ぶ。
方針：全 Hom を保つ二つの充満包含で、元の加群の零性を反映する。
規約：H⁰ の零対象への選び直しをしない。使われ方：実二軸と指定商 End の零左成分。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (J : Type w) (X : J → PerfectDGModule R D)
local notation "I" => dgSmallPerfectEnvelopeInclusion R D J X
local instance : (I).onClosed.Full :=
  (I).onClosed_full_of_homIso (fun _ _ => by change IsIso (𝟙 _); infer_instance)
local instance : (I).onClosed.Faithful :=
  (I).onClosed_faithful_of_homIso (fun _ _ => by change IsIso (𝟙 _); infer_instance)
local instance : (perfectDGModuleInclusion R D Set.univ).onClosed.Full := by
  dsimp [perfectDGModuleInclusion]; infer_instance
local instance : (perfectDGModuleInclusion R D Set.univ).onClosed.Faithful := by
  dsimp [perfectDGModuleInclusion]; infer_instance

/-- 同じ小模型の指定零対象は、元の閉零射圏の実零対象である。 -/
lemma dgSmallPerfectEnvelopeZero_isZero :
    IsZero (ForgetEnrichment.of (Complex R) (dgSmallPerfectEnvelopeZero R D J X)) := by
  apply IsZero.of_full_of_faithful_of_isZero (I).onClosed
  apply IsZero.of_full_of_faithful_of_isZero (perfectDGModuleInclusion R D Set.univ).onClosed
  exact moduleZero_isZero R D

end SerrePositivity.KST.SConstruction

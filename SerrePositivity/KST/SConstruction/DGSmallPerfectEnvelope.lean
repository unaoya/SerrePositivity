module
public import SerrePositivity.KST.SConstruction.DGRepresentableThickGeneration
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancement
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import Mathlib.Logic.Small.Set

/-! # 元の延長像を保持する小さい充満 Perf 模型
概要：小さい標準代表系に指定延長像・実零加群・元の全代表加群を加えた dg 模型。
方針：小さい四つの対象族の和集合の充満 dg 部分圏を取り、全 Hom をそのまま使う。
規約：全 Perf の Small 性は仮定しない。使われ方：実 LT 四角形の厳密 dg 入力。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (J : Type w) [Small.{u} J] (X : J → PerfectDGModule R D)

/-- 元の小代表・指定延長像・実零対象・全代表を含む具体的な対象集合。 -/
def dgSmallPerfectEnvelopeObjects : Set (PerfectDGModule R D) :=
  Set.range (fun x : SmallPerfectDGModuleOver R D Set.univ => x.val) ∪
    (Set.range X ∪ ({perfectDGModuleZero R D Set.univ} ∪
      Set.range (dgRepresentablePerfectPoint R D)))

/-- 指定延長像を実際の対象のまま含む、元の全 Perf の充満 dg 部分圏。 -/
abbrev DGSmallPerfectEnvelope :=
  DGFullSubcategory (PerfectDGModule R D) (dgSmallPerfectEnvelopeObjects R D J X)

omit [Small.{u} J] in
/-- 元の全 Perf の豊穣構造を、同じ実対象集合へ制限する。 -/
instance dgSmallPerfectEnvelopeEnrichment : DGCategory R (DGSmallPerfectEnvelope R D J X) :=
  dgFullSubcategoryEnrichment R (PerfectDGModule R D) (dgSmallPerfectEnvelopeObjects R D J X)

/-- 元の四つの小さい対象族から、実対象集合そのものの小ささを得る。 -/
instance dgSmallPerfectEnvelopeSmall : Small.{u} (DGSmallPerfectEnvelope R D J X) := by
  change Small.{u} (dgSmallPerfectEnvelopeObjects R D J X)
  unfold dgSmallPerfectEnvelopeObjects
  infer_instance

/-- 元の全 Hom を保持する、実 Perf 模型への包含。 -/
def dgSmallPerfectEnvelopeInclusion :
    DGFunctor R (DGSmallPerfectEnvelope R D J X) (PerfectDGModule R D) :=
  dgFullSubcategoryInclusion R (PerfectDGModule R D) (dgSmallPerfectEnvelopeObjects R D J X)

/-- 元の小さい標準代表は同じ実対象のまま含まれる。 -/
def dgSmallPerfectEnvelopeOfSmall (x : SmallPerfectDGModuleOver R D Set.univ) :
    DGSmallPerfectEnvelope R D J X := ⟨x.val, Or.inl ⟨x, rfl⟩⟩

/-- 指定した元の延長像も同じ実対象のまま含まれる。 -/
def dgSmallPerfectEnvelopeOfFamily (j : J) : DGSmallPerfectEnvelope R D J X :=
  ⟨X j, Or.inr (Or.inl ⟨j, rfl⟩)⟩

/-- 元の実零加群を保持する、同じ小さい模型の指定零対象。 -/
def dgSmallPerfectEnvelopeZero : DGSmallPerfectEnvelope R D J X :=
  ⟨perfectDGModuleZero R D Set.univ, Or.inr (Or.inr (Or.inl (Set.mem_singleton _)))⟩

/-- 元の代表加群を保持する、同じ小さい模型の指定対象。 -/
def dgSmallPerfectEnvelopeRepresentable (d : D) : DGSmallPerfectEnvelope R D J X :=
  ⟨dgRepresentablePerfectPoint R D d, Or.inr (Or.inr (Or.inr ⟨d, rfl⟩))⟩

end SerrePositivity.KST.SConstruction

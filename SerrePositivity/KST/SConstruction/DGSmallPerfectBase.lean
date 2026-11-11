module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeZero

/-! # 元の零加群と全代表を保持する小さい Perf 始域
概要：追加像族を空にし、元の標準小代表系・零加群・全代表を含む具体的小模型を固定する。
方針：構成済みの実像包含模型を空族に適用する。
規約：全 Perf の Small 性は仮定しない。使われ方：実 LT 四角形の共通始域。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 追加像を持たない元の実対象族。 -/
def dgSmallPerfectBaseFamily : Empty → PerfectDGModule R D := Empty.elim

/-- 元の標準小代表・実零加群・全代表を含む、小さい実 Perf 模型。 -/
abbrev DGSmallPerfectBase := DGSmallPerfectEnvelope R D Empty (dgSmallPerfectBaseFamily R D)

/-- 同じ小模型の指定零対象は元の零加群そのもの。 -/
def dgSmallPerfectBaseZero : DGSmallPerfectBase R D :=
  dgSmallPerfectEnvelopeZero R D Empty (dgSmallPerfectBaseFamily R D)

/-- 同じ小模型の元の代表対象。 -/
def dgSmallPerfectBaseRepresentable (d : D) : DGSmallPerfectBase R D :=
  dgSmallPerfectEnvelopeRepresentable R D Empty (dgSmallPerfectBaseFamily R D) d

/-- 同じ指定零加群の閉零対象性。 -/
lemma dgSmallPerfectBaseZero_isZero :
    IsZero (ForgetEnrichment.of (Complex R) (dgSmallPerfectBaseZero R D)) :=
  dgSmallPerfectEnvelopeZero_isZero R D Empty (dgSmallPerfectBaseFamily R D)

/-- 同じ小さい実 Perf 始域の native nerve は安定。 -/
lemma dgSmallPerfectBaseNerve_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectBase R D)) :=
  dgSmallPerfectEnvelopeNerve_isStable R D Empty (dgSmallPerfectBaseFamily R D)

end SerrePositivity.KST.SConstruction

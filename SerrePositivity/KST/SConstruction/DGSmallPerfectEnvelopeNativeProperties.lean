module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.SmallPerfectDGPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedQuasiEquivalenceForward
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectIdempotentCompleteGeneral

/-!
概要：S 構成の同じ小 Perf 包絡の前三角性と coherent 完備性を供給する。
方針：D の元小模型・実 Perf の性質を、元包含と評価同値で移す。
規約：元の指定実像を保持。使われ方：新しい中央射終域の native／固定 ν 比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (J : Type w) [Small.{u} J] (X : J → PerfectDGModule R D)

/-- 概要：同じ指定実像を含む小 Perf 包絡の dg 前三角性。
方針：元小代表系からの同じ準同値で D の前三角性を移す。
規約：全 Perf の Small 性は不要。使われ方：実中央射終域の完全性。 -/
lemma dgSmallPerfectEnvelope_pretriangulated :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGSmallPerfectEnvelope R D J X) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectDGModuleOver_isDGPretriangulated R D Set.univ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R D J X)
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R D J X)

omit [Small.{u} J] in
/-- 概要：同じ指定実像を含む小 Perf 包絡の coherent 冪等完備性。
方針：元実 Perf の完備性を同じ全評価同値で戻す。
規約：元の基底自体の完備性は仮定しない。使われ方：固定 ν の実頂点同値。 -/
lemma dgSmallPerfectEnvelope_complete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectEnvelope R D J X)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R D).of_equivalence
    (dgSmallPerfectEnvelopeNerveEquivalence R D J X).symm

end SerrePositivity.KST.SConstruction

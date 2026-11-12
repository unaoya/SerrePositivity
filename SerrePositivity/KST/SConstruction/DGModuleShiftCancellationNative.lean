module
public import SerrePositivity.KST.SConstruction.DGModuleShiftCancellationSpecifiedComposite
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInvNative

/-!
概要：元指定 shift 相殺の全厳密比較を native 全関手同型へ接続する。
方針：同じ元実相殺同型の閉射回収を全頂点に適用する。
規約：旧実相殺同型と全ホモトピーを保持する。
使われ方：元実逆回転全比較の相殺因子。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma mappedIsoRecovery {M N : ModuleCategory R D} (a : M ⟶ N) (e : M ≅ N)
    (h : a = e.hom) : IsIso ((moduleToHomotopy R D).map a) := by
  cases h
  infer_instance
local notation "A" => DGFunctor.comp (moduleShiftDG R D 1) (moduleShiftDG R D (-1))
local notation "I" => DGFunctor.id (RightModule R D)
local notation "θ" => dgModuleSpecifiedCancellationStrictComparison R D

/-- 概要：元指定相殺の全比較の閉成分は K(D) の同値。
方針：同じ元実相殺同型への閉射回収を使用する。
規約：元指定同型不変。使われ方：全相殺ホモトピーの頂点可逆性。 -/
lemma dgModuleSpecifiedCancellation_isIso (M : RightModule R D) :
    IsIso ((moduleToHomotopy R D).map (dgModuleNaturalConeArrow R D (A) (I) (θ) M)) :=
  mappedIsoRecovery R D _ (dgModuleSpecifiedCancellationIso R D M)
    (dgModuleSpecifiedCancellationStrictComparison_arrow R D M)

/-- 概要：同じ元指定相殺の全ホモトピーは全頂点で可逆。
方針：元閉射の同じ native 辺の回収と実同型を使う。
規約：同じ元ホモトピーを保持。使われ方：native 全相殺比較。 -/
lemma dgModuleSpecifiedCancellation_pointwise
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (θ).homotopy z).toTruncated := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  let a := dgModuleNaturalConeArrow R D (A) (I) (θ) M
  have hc : (θ).app M = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a) := by
    apply Subtype.ext
    exact (dgModuleNaturalConeArrow_cycle R D (A) (I) (θ) M).symm
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopy_vertex_edge (θ) M
  rw [hc] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D a (dgModuleSpecifiedCancellation_isIso R D M)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D a).toTruncated)

/-- 概要：元指定相殺を保持する native 全関手同型。
方針：元全ホモトピーと同じ閉実同型の可逆性を束ねる。
規約：旧実相殺と厳密一致。使われ方：元実逆回転全比較の終辺。 -/
def dgModuleSpecifiedCancellationNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (θ).homotopy (dgModuleSpecifiedCancellation_pointwise R D)
end SerrePositivity.KST.SConstruction

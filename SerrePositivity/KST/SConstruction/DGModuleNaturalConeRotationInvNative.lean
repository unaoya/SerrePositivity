module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInvComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTransIso

/-!
概要：同じ実全厳密回転逆を native dg nerve の全関手同型へ送る。
方針：元ホモトピーの各頂点辺を同じ元閉射へ戻し、K(D) 同値を反映する。
規約：点ごとの同型の選択ではなく、構成済み全ホモトピーを使用する。
使われ方：元逆回転後合成の全 native 比較の回転逆因子。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "T" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (T) (ν)
local notation "V" => F.comp (moduleShiftDG R D 1)
local notation "ρ" => dgModuleNaturalConeRotationInv R D F G η

/-- 概要：元全厳密回転逆の同じ native ホモトピーは全頂点で可逆。
方針：元閉射の厳密回収と同じ K(D) 成分同値を使用する。
規約：元全ホモトピーを保持。使われ方：実全関手同型への可逆性入力。 -/
lemma dgModuleNaturalConeRotationInv_pointwise
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (ρ).homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  let a := dgModuleNaturalConeArrow R D (U) (V) (ρ) x
  have hc : (ρ).app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a) := by
    apply Subtype.ext
    exact (dgModuleNaturalConeArrow_cycle R D (U) (V) (ρ) x).symm
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopy_vertex_edge (ρ) x
  rw [hc] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D a
    (dgModuleNaturalConeRotationInv_isIso R D F G η x)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D a).toTruncated)

/-- 概要：同じ元実回転逆の native 全関手同型。
方針：構成済み全ホモトピーと全頂点可逆性を直接束ねる。
規約：元上下関手・元全 Hom の作用を保持。
使われ方：実逆回転後合成全比較の回転逆因子。 -/
def dgModuleNaturalConeRotationInvNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (U)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (ρ).homotopy
    (dgModuleNaturalConeRotationInv_pointwise R D F G η)
end SerrePositivity.KST.SConstruction

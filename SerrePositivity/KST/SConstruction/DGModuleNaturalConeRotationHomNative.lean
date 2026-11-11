module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationHomComparison
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInvNative

/-!
概要：同じ元実回転比較の全ホモトピーを native 全関手同型として保持する。
方針：元全厳密自然変換の各辺を元実閉射へ回収し、K(D) 同値を反映する。
規約：元の全ホモトピーと指定回転成分を使用する。
使われ方：実 connecting cone 比較の回転因子。
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
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η

/-- 概要：元全回転比較の native ホモトピーは全頂点で可逆。
方針：同じ元閉射の回収と実 K(D) 成分同値を使う。
規約：元ホモトピーの頂点辺を保持。使われ方：native 全比較の可逆性。 -/
lemma dgModuleNaturalConeRotationHom_pointwise
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (γ).homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  let a := dgModuleNaturalConeArrow R D (FS) (U) (γ) x
  have hc : (γ).app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a) := by
    apply Subtype.ext
    exact (dgModuleNaturalConeArrow_cycle R D (FS) (U) (γ) x).symm
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopy_vertex_edge (γ) x
  rw [hc] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D a
    (dgModuleNaturalConeRotationHom_isIso R D F G η x)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D a).toTruncated)

/-- 概要：同じ元実回転比較を保持する native 全関手同型。
方針：元全ホモトピーと実証済み全頂点可逆性を束ねる。
規約：回転逆の任意の逆で置き換えない。
使われ方：実 connecting cone の合成全比較の回転因子。 -/
def dgModuleNaturalConeRotationHomNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (FS)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (U)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (γ).homotopy
    (dgModuleNaturalConeRotationHom_pointwise R D F G η)
end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecomposition
public import SerrePositivity.KST.SConstruction.DGModuleConeHomotopyTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTransIso

/-!
概要：元前合成 cone 比較を同じ native 全関手同型へ送る。
方針：指定前比較の K(D) 同値を元実 cone 射へ反映する。
規約：構成済みの同じ全ホモトピーを使用する。
使われ方：入力同型を保つ実 connecting cone の全比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G H : DGFunctor R P (RightModule R D))
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H)
local notation "γ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α β
local notation "CB" => dgModuleNaturalConeFunctor R D G H β
local notation "CC" => dgModuleNaturalConeFunctor R D F H (γ)
local notation "θ" => dgModuleNaturalConePrecomposition R D F G H α β
variable (ha : ∀ x, IsIso ((moduleToHomotopy R D).map
  (dgModuleNaturalConeArrow R D F G α x)))
include ha

/-- 概要：元前合成 cone 比較の同じ閉射は K(D) 同値。
方針：元前辺と恒等後辺に実 cone 射の三角形判定を使う。
規約：同じ零ホモトピーを保持。使われ方：native 可逆性。 -/
lemma dgModuleNaturalConePrecomposition_isIso (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (CC) (CB) (θ) x)) := by
  rw [dgModuleNaturalConePrecomposition_arrow]
  apply dgModuleConeMapOfHomotopy_isIso
  · exact ha x
  · rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- 概要：同じ前合成 cone ホモトピーは全頂点で可逆。
方針：元閉成分を回収して同じ K(D) 可逆性を使う。
規約：元全ホモトピー不変。使われ方：native 全比較への束ね。 -/
lemma dgModuleNaturalConePrecomposition_pointwise (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (θ).homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  let a := dgModuleNaturalConeArrow R D (CC) (CB) (θ) x
  have hc : (θ).app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a) := by
    apply Subtype.ext
    exact (dgModuleNaturalConeArrow_cycle R D (CC) (CB) (θ) x).symm
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopy_vertex_edge (θ) x
  rw [hc] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D a
    (dgModuleNaturalConePrecomposition_isIso R D F G H α β ha x)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D a).toTruncated)

/-- 概要：指定前合成 cone 比較の同じ native 全関手同型。
方針：元全ホモトピーと実証済み全頂点可逆性を束ねる。
規約：任意の成分同値で置き換えない。使われ方：元実逆回転の入力比較。 -/
def dgModuleNaturalConePrecompositionNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CC)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CB)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (θ).homotopy
    (dgModuleNaturalConePrecomposition_pointwise R D F G H α β ha)
end SerrePositivity.KST.SConstruction

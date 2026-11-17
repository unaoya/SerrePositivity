module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointAugmentation

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のBEモデル源で全弱自然変換を同じ全関手同型へ送る。
方針：元の局所化の弱辺反転を同じ全自然変換の全成分へ適用する。
規約：元のモデル源と元の自然変換を保つ。
使われ方：全source-frameのpairingの元の標的置換を全図式で外す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
variable (A : Type u) [CommRing A]
local instance modelWeakTransformationModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 元の全弱自然変換は、元の同じモデル源で全関手同型になる。 -/
def strictBETotModelWeakTransformationIso
    {J : Type (u+1)} [SmallCategory J]
    {F G : J ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (η : F ⟶ G)
    (hη : ∀ j, weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (AsSmall.down.map (η.app j))) :
    FunctorIso (nerveMap F ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) (nerveMap G ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) := by
  apply nerveTransformationPostIso η (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
  intro j
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_isLocalization A).choose
    (show (nerve.edgeMk (η.app j)).edge ∈
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) from
        ⟨_, _, _, hη j, rfl⟩)
  change IsInvertibleEdge (X := _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) ((edgeOfSimplex (nerve.edgeMk (η.app j)).edge).map
    ((SSet.truncation 2).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) at h
  exact (isInvertibleEdge_congr (X := _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)
    (e := (edgeOfSimplex (nerve.edgeMk (η.app j)).edge).map
      ((SSet.truncation 2).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)))
    (f := ((nerve.edgeMk (η.app j)).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)).toTruncated) rfl).mp h
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

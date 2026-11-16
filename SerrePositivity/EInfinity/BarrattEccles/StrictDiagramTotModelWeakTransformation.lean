module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointAugmentation

/-!
概要：元のBEモデル源で全弱自然変換を同じ全関手同型へ送る。
方針：元の局所化の弱辺反転を同じ全自然変換の全成分へ適用する。
規約：元のモデル源と元の自然変換を保つ。
使われ方：全source-frameのpairingの元の標的置換を全図式で外す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
variable (A : Type u) [CommRing A]
local instance modelWeakTransformationModel : ModelCategory (operad A).Algebra := modelCategory A

/-- 元の全弱自然変換は、元の同じモデル源で全関手同型になる。 -/
def strictBETotModelWeakTransformationIso
    {J : Type (u+1)} [SmallCategory J]
    {F G : J ⥤ AsSmall.{u+1} (operad A).Algebra} (η : F ⟶ G)
    (hη : ∀ j, weakEquivalences (operad A).Algebra (AsSmall.down.map (η.app j))) :
    FunctorIso (nerveMap F ≫ strictBETotModelSource A) (nerveMap G ≫ strictBETotModelSource A) := by
  apply nerveTransformationPostIso η (strictBETotModelSource A)
  intro j
  have h := (strictBETotModelSource_isLocalization A).choose
    (show (nerve.edgeMk (η.app j)).edge ∈
      SimplicialLocalization.weakNerveEdges (modelRelativeCategory (operad A).Algebra) from
        ⟨_, _, _, hη j, rfl⟩)
  change IsInvertibleEdge (X := CAlg_R A) ((edgeOfSimplex (nerve.edgeMk (η.app j)).edge).map
    ((SSet.truncation 2).map (strictBETotModelSource A))) at h
  exact (isInvertibleEdge_congr (X := CAlg_R A)
    (e := (edgeOfSimplex (nerve.edgeMk (η.app j)).edge).map
      ((SSet.truncation 2).map (strictBETotModelSource A)))
    (f := ((nerve.edgeMk (η.app j)).map (strictBETotModelSource A)).toTruncated) rfl).mp h
end SerrePositivity.EInfinity.BarrattEccles

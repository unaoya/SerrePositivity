module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotModelSource
public import SerrePositivity.EInfinity.BarrattEccles.RightFrames
public import SerrePositivity.EInfinity.BarrattEccles.MappingFactorizations
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelRightFrameComparison

/-!
概要：同じBE right frameの実Homと、元の全CAlg源のnative pinched Homを比較する。
方針：既存の一般モデル圏の比較へ、同じBEモデル・frame・全局所化を代入。
規約：IS-W2 R03の係数移送・表示の法則。全代数源・同じ比較を保持。
使われ方：実frame錐と指定native全Tot錐の制限比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance : ModelCategory (operad A).Algebra := modelCategory A
local instance : (cofibrations (operad A).Algebra).HasFunctorialFactorization
    (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
attribute [local instance] rightFrameHom_kanComplex

/-- 同じ全BE源の両端を持つ、実right frame Homとnative pinched Homの全同値。 -/
def strictBETotRightFramePinchedEquivalence
    (X : (operad A).Algebra) [IsCofibrant X] (Y : (operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj ((rightFrameHom (rightFrameFamily A) X).obj Y))
      (pinchedHom ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) := by
  have h := SimplicialLocalization.modelRightFramePinchedEquivalence (rightFrameFamily A)
    (strictBETotModelSource A) (strictBETotModelSource_isLocalization A) X Y
  simpa only [strictBETotModelSource_vertex] using h

end SerrePositivity.EInfinity.BarrattEccles

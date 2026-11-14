module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotRightFrameComparison

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
local instance strictBETotCoherentModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotCoherentFactorization : (cofibrations (operad A).Algebra).HasFunctorialFactorization
    (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
attribute [local instance] rightFrameHom_kanComplex

/-- 同じ実right frame比較は、全標的のcoherent比較とCAlg源の指定二胞体を共に持つ。 -/
def strictBETotRightFrameCoherentComparison
    (X : (operad A).Algebra) [IsCofibrant X] :
    (FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X) (rightFrameFamily A) 0)
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X) (rightFrameFamily A) 6)) ×
      FrameHom.CoherentLocalizationComparison
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)) (strictBETotModelSource A) :=
  SimplicialLocalization.modelRightFrameCoherentComparison (rightFrameFamily A)
    (strictBETotModelSource A) (strictBETotModelSource_isLocalization A) X

end SerrePositivity.EInfinity.BarrattEccles

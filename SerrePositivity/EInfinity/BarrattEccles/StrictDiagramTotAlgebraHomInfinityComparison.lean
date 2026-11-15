module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeHomInfinityComparison
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotModelSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationInput

/-!
概要：同じ全Hom比較を、元の全BE代数源・元の同じstrict図式上で読む。
方針：元の全nerve包含を前合成し、全単体の源の一致と同じ評価で照合。
規約：IS-W2 R03の係数移送・自然性の法則。高次自然性を保持する。
使われ方：元の同じ重み付き錐とnative錐の右境界の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotAlgebraHomInfinityModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotAlgebraHomInfinityFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotAlgebraHomInfinityCofibrant (X : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A X) := framedLimitProbe_cofibrant A X

/-- 元の全代数nerve上の実frame Homは、元のalgebraCAlgSourceの正本Homと全同型。 -/
def strictBEAlgebraProbeHomInfinityIso (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
            (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (algebraCAlgSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  have h := (strictBETotProbeFrameHomInfinityIso A X).precomp
    ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A))
  simpa only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    strictBETotModelSource_up] using h

/-- 元の同じstrict BE図式の全nerveに沿う正本Homとの全比較。 -/
def strictBETotDiagramProbeHomInfinityIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra)
    (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F) ≫
        (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
          FrameHom.rightFrameHammockCoherentDiagram
            ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
              (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialDiagram A F) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  have h := (strictBEAlgebraProbeHomInfinityIso A X).precomp
    ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F))
  simpa only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    strictBECosimplicialDiagram] using h

end SerrePositivity.EInfinity.BarrattEccles

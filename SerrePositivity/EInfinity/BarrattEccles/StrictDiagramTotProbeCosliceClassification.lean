module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotAlgebraHomInfinityComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HomCovariantComparison

/-!
概要：BEの元の全frame Hom比較を、同じ頂点の元のcosliceの分類へ結ぶ。
方針：既存の全Hom∞同型と既存の共変表現可能関手の全coslice比較を合成する。
規約：IS-W2 R02〜R03の既存比較の合成則。値ごとの同値で代用しない。
使われ方：同じ指定BK錐から同じnative join錐へ進む分類図式の照合。
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
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotCosliceClassificationModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotCosliceClassificationFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotCosliceClassificationCof (X : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A X) := framedLimitProbe_cofibrant A X

/-- 元の代数全nerve上の同じframe比較を、同じ元のcosliceの全分類へ合成する。 -/
def strictBEAlgebraProbeCosliceClassificationIso (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
            (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (algebraCAlgSource A) ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))))) :=
  (strictBEAlgebraProbeHomInfinityIso A X).trans
    (FunctorIso.precomp ((homInfinityCovariant_covariantIso _).trans
      (covariantRepresentableInfinity_cosliceIso _))
        ((SSet.uliftFunctor.{u+2,u+1}).map (algebraCAlgSource A)))

/-- 同じstrictな全図式へ引き戻した、同じ頂点のcosliceの全分類比較。 -/
def strictBETotDiagramProbeCosliceClassificationIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F) ≫
        (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
          FrameHom.rightFrameHammockCoherentDiagram
            ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
              (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialDiagram A F) ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))))) := by
  have h := (strictBEAlgebraProbeCosliceClassificationIso A X).precomp
    ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F))
  simpa only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    strictBECosimplicialDiagram] using h

end SerrePositivity.EInfinity.BarrattEccles

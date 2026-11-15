module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeKanDiagram
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeHomInfinityComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HomCovariantComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportComparison

/-!
概要：同じBK係数のweighted nerveの全分類を、元の頂点のcosliceの全分類と比較する。
方針：既存のweighted nerve単位・全frame比較・coslice分類を同じ底で合成する。
規約：IS-W2 R02〜R03の既存比較の合成則。点ごとの分類を全自然性の代用にしない。
使われ方：指定BK切断をnative錐へ運ぶ相対写像空間の入力。
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
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotBKClassificationModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotBKClassificationFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotBKClassificationCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

/-- 同じ大きい添字における、元のCAlg源への全図式。 -/
def strictBETotUniverseDiagram (F : K ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ)) ⟶
      (SSet.uliftFunctor.{u+2,u+1}).obj (CAlg_R A) :=
  (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotProbeFrameIndex A K F)) ≫
    (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A)

/-- 同じ全Kan係数は、同じ元の頂点のcosliceの全分類と比較される。 -/
def strictBETotKanDiagramCosliceIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso (kanDiagramCoherentNerve (strictBETotProbeKanDiagram A K F Y))
      (strictBETotUniverseDiagram A K F ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))))) := by
  rw [strictBETotProbeKanDiagram_coherent]
  have h := (strictBETotProbeFrameHomInfinityIso A Y).precomp
    ((SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotProbeFrameIndex A K F)))
  have h' : FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotProbeFrameIndex A K F)) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
            (framedLimitProbe A Y)) (rightFrameFamily A) 0)
      (strictBETotUniverseDiagram A K F ≫ homInfinityCovariant
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) := by
    simpa only [strictBETotUniverseDiagram, Category.assoc] using h
  exact h'.trans (FunctorIso.precomp
    ((homInfinityCovariant_covariantIso _).trans (covariantRepresentableInfinity_cosliceIso _))
      (strictBETotUniverseDiagram A K F))

/-- 同じBK係数のweighted nerveの分類から、同じ頂点のcosliceの分類への全同型。 -/
def strictBETotBKClassificationIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso
      (leftStraighteningCandidate ((weightedNerveKanEnriched (AsSmall.{u+1} Kᵒᵖᵒᵖ)).obj
        ⟨strictBETotProbeKanDiagram A K F Y, trivial⟩).val.hom)
      (strictBETotUniverseDiagram A K F ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))))) :=
  (weightedNerveStraighteningUnitIso (strictBETotProbeKanDiagram A K F Y)).symm.trans
    (strictBETotKanDiagramCosliceIso A K F Y)

end SerrePositivity.EInfinity.BarrattEccles

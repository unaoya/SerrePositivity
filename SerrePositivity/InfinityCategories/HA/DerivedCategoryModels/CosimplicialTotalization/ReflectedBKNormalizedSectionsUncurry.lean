module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorAW
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedWeightSectionInverseEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWRawCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeAWStandardCutComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeTopEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomParameterNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexNativeParameterEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWCutFaces

/-!
概要：同じA09比較の全標準単体でのuncurryを元の豊穣合成へ同定する。
方針：一般の逆自由随伴評価と、元の実AWの複体射の等式を合成する。
規約：全標準単体パラメータ・全切断点と指定比較射を保持する既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02のraw AW全切断和の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CochainComplex HomComplex HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial TensorProduct
variable {A : Type u} [CommRing A]

/-- 同じA09の全標準単体をuncurryすると、元の錐入力との実豊穣合成を返す。 -/
theorem reflectedBKNormalizedSections_uncurry
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    (weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
        ((normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y) φ).app (Opposite.op m)
            (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
              ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))))).app j =
      (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
        standardDoldKanSpaceMap P Q := by
  dsimp only
  let T := (productTotalFunctor A).obj X
  let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
  let S := (reflectedNormalizedBKSmallWeight A).obj j
  let B := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)
  let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
    (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
      (forget (ModuleCat A))).inv
  let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
  let Y := (homDiagramFunctor P).obj X
  let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
    (reflectedNormalizedBKSmallHomIso A Y).hom
  let W := reflectedNormalizedBKSmallWeight A
  let H := normalizedBKSmallDiagram A Y
  let β := ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
    ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α)
  apply (Equiv.injective (((freeNegativeChainsAdjunction A).homEquiv (S ⊗ B)
    (homObject A (Complex A) P Q)).symm))
  exact (normalizedWeightSectionMap_uncurry_inverse_app A W H φ m β j).trans
    (reflectedBKFreeTensor_inverse_AW φ P X m α j)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

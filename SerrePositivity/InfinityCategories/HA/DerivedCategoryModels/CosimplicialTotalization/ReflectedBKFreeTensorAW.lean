module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWRawCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeAWStandardCutComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeTopEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomParameterNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexNativeParameterEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWCutFaces

/-!
概要：同じA09逆射のAW前合成を元の豊穣合成の逆自由随伴と同定する。
方針：既証明の全切断を有限和にまとめ、raw生成元の制限則で全複体射へ戻す。
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
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial TensorProduct
variable {A : Type u} [CommRing A]

/-- 同じ実パラメータのAW前合成は、元の実豊穣合成の逆自由随伴そのもの。 -/
theorem reflectedBKFreeTensor_inverse_AW
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
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
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
          ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))
    freeProductAlexanderWhitney φ S B ≫ t.app j =
      ((freeNegativeChainsAdjunction A).homEquiv (S ⊗ B) (homObject A (Complex A) P Q)).symm
        ((g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
          standardDoldKanSpaceMap P Q) := by
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
  let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
    (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
      (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
        ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))
  change freeProductAlexanderWhitney φ S B ≫ t.app j =
    ((freeNegativeChainsAdjunction A).homEquiv (S ⊗ B) (homObject A (Complex A) P Q)).symm
      ((g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
        standardDoldKanSpaceMap P Q)
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i ≤ 0
  · have he : -(((-i).toNat : ℕ) : ℤ) = i := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    generalize hn : (-i).toNat = n at he
    subst i
    change (freeProductAlexanderWhitney φ S B).f (-(n : ℤ)) ≫
      (t.app j).f (-(n : ℤ)) = _
    apply freeProductAlexanderWhitney_f_eq_of_raw φ S B n
    intro w a
    exact freeProductAW_standard_raw_value φ S B P T Q g f (t.app j) n w a (by
      intro c
      exact (reflectedBKFreeTensor_inverse_cut P X m α j n c w a).trans
        (awTerm_univ_top_faces (g.app _ w) (f.app _ a) c))
  · exact (((normalizedMooreComplex (ModuleCat A)).obj ((S ⊗ B) ⋙ ModuleCat.free A)).isZero_extend_X
      ComplexShape.embeddingDownNat i
        (fun n hn => by change -(n : ℤ) = i at hn; omega)).eq_of_src _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

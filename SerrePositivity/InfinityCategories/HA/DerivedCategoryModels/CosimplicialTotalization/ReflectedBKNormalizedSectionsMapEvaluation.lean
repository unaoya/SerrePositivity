module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKNormalizedSectionsUncurry
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedWeightSectionInverseEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWRawCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeAWStandardCutComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeTopEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomParameterNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexNativeParameterEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWCutFaces

/-!
概要：同じA09比較の全uncurryを元の豊穣合成へ同定する。
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

/-- 指定比較の全uncurryの各点は、元の錐入力と全パラメータとの実豊穣合成。 -/
theorem reflectedBKNormalizedSections_uncurry_map
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let ψ := standardDoldKanSpaceMap P T ≫ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map γ ≫
      normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A Y) φ
    (weightedSectionsUncurry ψ).app j =
      (g ⊗ₘ 𝟙 (standardHomSpace (R := A) P T)) ≫ (β_ _ _).hom ≫
        standardComposition (R := A) P T Q ≫ standardDoldKanSpaceMap P Q := by
  dsimp only
  let T := (productTotalFunctor A).obj X
  let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
  let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
    (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
      (forget (ModuleCat A))).inv
  let Y := (homDiagramFunctor P).obj X
  let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
    (reflectedNormalizedBKSmallHomIso A Y).hom
  let ψ := standardDoldKanSpaceMap P T ≫ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map γ ≫
    normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
      (normalizedBKSmallDiagram A Y) φ
  apply NatTrans.ext
  funext n
  obtain ⟨m⟩ := n
  apply ConcreteCategory.hom_ext
  rintro ⟨w, α⟩
  let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
  let a0 := ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 m))
  have hf := liftedStandardSimplexHomIso_yoneda_apply (standardHomSpace (R := A) P T) m α
  rw [liftedStandardSimplexHomIso_hom_apply] at hf
  have hparam : f ≫ ψ = liftedStandardSimplexIso.{u}.hom.app m ≫
      SSet.yonedaEquiv.symm (ψ.app (Opposite.op m) α) := by
    dsimp only [f]
    rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
    rfl
  have hp := congrArg (fun k => k.app j) (weightedSectionsUncurry_precomp f ψ)
  have hs := congrArg (fun h => (weightedSectionsUncurry h).app j) hparam
  have hh : (((reflectedNormalizedBKSmallWeight A).obj j) ◁ f) ≫
      (weightedSectionsUncurry ψ).app j =
      (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
        standardDoldKanSpaceMap P Q :=
    hp.symm.trans (hs.trans (reflectedBKNormalizedSections_uncurry φ P X m α j))
  have hv := congrArg (fun h => h.app (Opposite.op m) (w, a0)) hh
  change ((weightedSectionsUncurry ψ).app j).app (Opposite.op m)
      (w, f.app (Opposite.op m) a0) =
    (standardDoldKanSpaceMap P Q).app (Opposite.op m)
      ((standardComposition (R := A) P T Q).app (Opposite.op m)
        (f.app (Opposite.op m) a0, g.app (Opposite.op m) w)) at hv
  change f.app (Opposite.op m) a0 = α at hf
  rw [hf] at hv
  exact hv

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

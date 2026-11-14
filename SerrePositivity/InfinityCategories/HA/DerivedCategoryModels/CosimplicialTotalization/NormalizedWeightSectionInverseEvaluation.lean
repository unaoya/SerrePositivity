module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeAdjunction

/-!
概要：同じA09の指定uncurryの各点を元の逆自由随伴で評価する。
方針：同じtensor Hom同型の両逆、uncurry則、図式随伴の各点での逆射則を合成する。
規約：任意の図式と全単体パラメータに関する既存構成の法則。計算上限を変えない。
使われ方：HA 1.2.4、IS-W2 B02の大きな実パラメータへの適用の証明分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]

/-- 元の図式自由随伴を各点で逆自由随伴へ戻すと同じ複体射。 -/
theorem freeNegativeChainsDiagramAdjunction_hom_symm_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (f : freeNegativeChainsDiagram (A := A) W ⟶ Q) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv (W.obj j) (Q.obj j)).symm
      ((((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q) f).app j) = f.app j := by
  have hr := freeNegativeChainsDiagramAdjunction_symm_app W Q
    (((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q) f) j
  have ha := congrArg (fun k => k.app j)
    (((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q).symm_apply_apply f)
  exact hr.symm.trans ha

/-- 指定tensor Homの順方向からのuncurryは元のAW前合成へ戻る。 -/
theorem normalizedWeightSectionMap_hom_uncurry_inverse_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (φ : simplicialRingCoefficient.{u} →+* A) (m : SimplexCategory)
    (f : (freeTensorFrame A W (liftedStandardSimplexParameter J)).obj m ⟶ Q) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv
      (W.obj j ⊗ (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) (Q.obj j)).symm
      ((weightedSectionsUncurry
        (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
          ((normalizedWeightSectionMap A W Q φ).app (Opposite.op m)
            ((freeTensorDiagramHomIso A Q W).hom.app (Opposite.op m) f)))).app j) =
    freeProductAlexanderWhitney φ (W.obj j)
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) ≫ f.app j := by
  have hp := congrArg (fun k => ((freeNegativeChainsAdjunction A).homEquiv
    (W.obj j ⊗ (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) (Q.obj j)).symm
      (k.app j)) (normalizedWeightSectionMap_hom_uncurry A W Q φ m f)
  exact hp.trans (freeNegativeChainsDiagramAdjunction_hom_symm_app A _ Q
    (freeProductDiagramAW φ W ((liftedStandardSimplexParameter J).obj m) ≫ f) j)

/-- 指定A09のuncurryの各点の逆自由随伴は、元のAWと指定tensor逆射の合成。 -/
theorem normalizedWeightSectionMap_uncurry_inverse_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (φ : simplicialRingCoefficient.{u} →+* A) (m : SimplexCategory)
    (β : ((truncatedDoldKanFunctor A).obj (linearHomComplex A
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) W))
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj Q))).obj (Opposite.op m)) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv
      (W.obj j ⊗ (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) (Q.obj j)).symm
      ((weightedSectionsUncurry
        (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
          ((normalizedWeightSectionMap A W Q φ).app (Opposite.op m) β))).app j) =
    freeProductAlexanderWhitney φ (W.obj j)
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) ≫
        ((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m) β).app j := by
  let e := freeTensorDiagramHomIso A Q W
  obtain ⟨f, hf⟩ := CategoryTheory.surjective_of_epi (e.hom.app (Opposite.op m)) β
  subst β
  have hi := ConcreteCategory.congr_hom (Iso.hom_inv_id_app e (Opposite.op m)) f
  change e.inv.app (Opposite.op m) (e.hom.app (Opposite.op m) f) = f at hi
  have hr := congrArg (fun t => freeProductAlexanderWhitney φ (W.obj j)
    ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) ≫ t.app j) hi
  exact (normalizedWeightSectionMap_hom_uncurry_inverse_app A W Q φ m f j).trans hr.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

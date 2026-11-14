module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomSourceCochainEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKSmallHom
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKReversePrecomposition

/-!
概要：A12の実際の反転・係数重みHom移送を同じ始域射の前合成として評価する。
方針：既存始域同型とAsSmall制限の成分を展開し、閉零射の前合成をまとめる。
規約：元のA12の同型・Moore反転と全斉次射を保持する既存構成の法則。
使われ方：HA 1.2.4、IS-W2 B02のBK行合成則との厳密な接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
local notation "E" => functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (ComplexShape.up ℤ)
local notation "V" => Functor.flip (Functor.obj SimplicialObject.opFunctor bousfieldKanSetWeight)

/-- A12の指定係数重み移送は同じ逆重み射の前合成とAsSmall制限である。 -/
theorem reflectedNormalizedBKSmallHomIso_hom_apply (X : CosimplicialObject (Complex A))
    (p : ℤ) (z : (reflectedNormalizedBKHom X).X p) :
    (reflectedNormalizedBKSmallHomIso A X).hom.f p z =
      asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ)
        ((E).obj (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})))
        ((E).obj (doubleOppositeDiagram X)) p
        ((Cochain.ofHom (normalizedLinearWeightDiagramIso A V).inv).comp z (zero_add p)) := by
  change asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ) _ _ p
    ((linearHomSourceIso A (normalizedLinearWeightDiagramIso A V)
      ((E).obj (doubleOppositeDiagram X))).hom.f p z) = _
  rw [linearHomSourceIso_hom_apply]

/-- 同じA12の反転・係数重み移送の合成は二つの指定重み射の合成の前合成。 -/
theorem reflectedNormalizedBKSmallHomIso_reverse_apply (X : CosimplicialObject (Complex A))
    (p : ℤ) (z : (normalizedBousfieldKanHom X).X p) :
    (reflectedNormalizedBKSmallHomIso A X).hom.f p
      ((normalizedBKReverseHomotopyEquiv X).hom.f p z) =
      asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ)
        ((E).obj (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})))
        ((E).obj (doubleOppositeDiagram X)) p
        ((Cochain.ofHom ((normalizedLinearWeightDiagramIso A V).inv ≫
          extendMap (normalizedMooreReverse.app
            (linearizedSimplicialWeight A bousfieldKanSetWeight))
            ComplexShape.embeddingDownNat)).comp z (zero_add p)) := by
  let τ := extendMap (normalizedMooreReverse.app
    (linearizedSimplicialWeight A bousfieldKanSetWeight)) ComplexShape.embeddingDownNat
  have hr : (normalizedBKReverseHomotopyEquiv X).hom.f p z =
      (Cochain.ofHom τ).comp z (zero_add p) := by
    rw [normalizedBKReverseHomotopyEquiv_hom]
    exact intervalHomPrePost_id_apply A τ p z
  have hpre := congrArg (fun t : Cochain
      (reflectedNormalizedBKWeight.extend ComplexShape.embeddingDownNat)
      ((E).obj (doubleOppositeDiagram X)) p =>
        (Cochain.ofHom (normalizedLinearWeightDiagramIso A V).inv).comp t (zero_add p)) hr
  have hc := zeroSourcePrecomp_comp (normalizedLinearWeightDiagramIso A V).inv τ p z
  rw [reflectedNormalizedBKSmallHomIso_hom_apply]
  exact congrArg (asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ)
    ((E).obj (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})))
    ((E).obj (doubleOppositeDiagram X)) p) (hpre.trans hc)


end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeHomComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedPointwiseBousfieldKanCone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKSourceEvaluation

/-!
概要：元の反転BK錐入力を同じ自由鎖随伴の像に厳密に同定する。
方針：指定係数重み同型の両逆と既存の線形重みHom比較を使う。
規約：同じ錐代表・Moore反転・点ごとのΓ比較を保つ既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02の実錐入力と自由重み成分の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory HomologicalComplex CochainComplex HomComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A]
local notation "V" => Functor.flip (Functor.obj SimplicialObject.opFunctor bousfieldKanSetWeight)

/-- 元の反転点ごとの錐入力は、同じ係数重み逆射と錐代表の自由随伴像。 -/
theorem reversedWeightPointwiseBousfieldKanCone_freeAdjunction
    (X : CosimplicialObject (Complex A)) :
    reversedWeightPointwiseBousfieldKanCone X =
      (freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
        (V ⋙ SSet.uliftFunctor.{u,0})
        (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))
        ((functorComplexExchangeUnitIso (SimplexCategoryᵒᵖᵒᵖ) (ModuleCat A) (.up ℤ)).hom.app
            (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})) ≫
          complexOfFunctorsToFunctorToComplex.map
            ((normalizedLinearWeightDiagramIso A V).inv ≫
              reflectedBousfieldKanConeRepresentative X)) := by
  have h := normalizedLinearWeightHomEquiv_freeDiagram A V (bousfieldKanConeHomDiagram X)
    ((normalizedLinearWeightDiagramIso A V).inv ≫ reflectedBousfieldKanConeRepresentative X)
  rw [Iso.hom_inv_id_assoc] at h
  exact h

/-- 元の反転錐代表は、同じMoore反転と元の錐代表の実複体射の合成。 -/
theorem reflectedBousfieldKanConeRepresentative_source (X : CosimplicialObject (Complex A)) :
    reflectedBousfieldKanConeRepresentative X =
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat ≫ normalizedBousfieldKanConeRepresentative X := by
  have h := (normalizedBKReverseHomotopyEquiv_coneRepresentative X).symm.trans
    (normalizedBKReverseHomotopyEquiv_ofHom _ (normalizedBousfieldKanConeRepresentative X))
  exact Cochain.ofHom_injective h

/-- 元の反転錐入力を同じ自由随伴で戻すと、実A12の同じ始域射を前合成した代表となる。 -/
theorem reversedWeightPointwiseBousfieldKanCone_free_inverse
    (X : CosimplicialObject (Complex A)) :
    ((freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
      (V ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))).symm
      (reversedWeightPointwiseBousfieldKanCone X) =
      (functorComplexExchangeUnitIso (SimplexCategoryᵒᵖᵒᵖ) (ModuleCat A) (.up ℤ)).hom.app
          (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})) ≫
        complexOfFunctorsToFunctorToComplex.map
          (((normalizedLinearWeightDiagramIso A V).inv ≫
            extendMap (normalizedMooreReverse.app
              (linearizedSimplicialWeight A bousfieldKanSetWeight))
                ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X) := by
  rw [reversedWeightPointwiseBousfieldKanCone_freeAdjunction, Equiv.symm_apply_apply]
  have h := congrArg (fun t =>
    (functorComplexExchangeUnitIso (SimplexCategoryᵒᵖᵒᵖ) (ModuleCat A) (.up ℤ)).hom.app
        (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})) ≫
      complexOfFunctorsToFunctorToComplex.map ((normalizedLinearWeightDiagramIso A V).inv ≫ t))
    (reflectedBousfieldKanConeRepresentative_source X)
  simpa only [Category.assoc] using h

/-- 同じ逆随伴の各点・各複体次数の成分は元の実代表の成分そのもの。 -/
theorem reversedWeightPointwiseBousfieldKanCone_free_inverse_app_f
    (X : CosimplicialObject (Complex A)) (j : SimplexCategoryᵒᵖᵒᵖ) (i : ℤ) :
    ((((freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
      (V ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))).symm
      (reversedWeightPointwiseBousfieldKanCone X)).app j).f i =
      ((((normalizedLinearWeightDiagramIso A V).inv ≫
        extendMap (normalizedMooreReverse.app
          (linearizedSimplicialWeight A bousfieldKanSetWeight)) ComplexShape.embeddingDownNat) ≫
          normalizedBousfieldKanConeRepresentative X).f i).app j := by
  rw [reversedWeightPointwiseBousfieldKanCone_free_inverse]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- 自由鎖図式随伴の逆射の各点は、同じ自由鎖随伴の逆射。 -/
theorem freeNegativeChainsDiagramAdjunction_symm_app {J : Type*} [Category* J]
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (f : W ⟶ Q ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) (j : J) :
    (((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q).symm f).app j =
      ((freeNegativeChainsAdjunction A).homEquiv (W.obj j) (Q.obj j)).symm (f.app j) := by
  simp only [freeNegativeChainsDiagramAdjunction, Adjunction.homEquiv_symm_apply,
    NatTrans.comp_app, Adjunction.whiskerRight_counit_app_app]
  rfl

/-- 元の反転錐入力の各点の自由随伴逆像も、同じ実A12代表の全複体成分を返す。 -/
theorem reversedWeightPointwiseBousfieldKanCone_point_inverse_f
    (X : CosimplicialObject (Complex A)) (j : SimplexCategoryᵒᵖᵒᵖ) (i : ℤ) :
    (((freeNegativeChainsAdjunction A).homEquiv
      ((V ⋙ SSet.uliftFunctor.{u,0}).obj j)
      ((complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X)).obj j)).symm
      ((reversedWeightPointwiseBousfieldKanCone X).app j)).f i =
      ((((normalizedLinearWeightDiagramIso A V).inv ≫
        extendMap (normalizedMooreReverse.app
          (linearizedSimplicialWeight A bousfieldKanSetWeight)) ComplexShape.embeddingDownNat) ≫
          normalizedBousfieldKanConeRepresentative X).f i).app j := by
  have h := congrArg (fun t => HomologicalComplex.Hom.f t i)
    (freeNegativeChainsDiagramAdjunction_symm_app (V ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))
      (reversedWeightPointwiseBousfieldKanCone X) j)
  exact h.symm.trans (reversedWeightPointwiseBousfieldKanCone_free_inverse_app_f X j i)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

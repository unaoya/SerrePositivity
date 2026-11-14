module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeSourceNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBousfieldKanSetCone
public import SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHomNaturality

/-!
概要：同じ指定BK錐の双方向自然性を実切断・Γ・集合的重みへ移す。
方針：既存の正規化線形重みHom同値の全標的射への自然性を適用する。
規約：IS-W2 D01の既存構成の係数移送則。全単体・元の反転符号を保つ。
使われ方：HA 1.2.4、同じ実錐の全図式パラメータへの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A]

/-- 同じHom複体図式から実切断・Γ・忘却で得る全単体図式の全関手。 -/
def bousfieldKanSetHomFunctor :
    CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ ⥤
      SimplicialObject (SimplexCategoryᵒᵖᵒᵖ ⥤ Type u) :=
  (ComplexShape.embeddingUpIntLE 0).truncLE'Functor _ ⋙ Abelian.DoldKan.Γ ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
      ((Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (Type u)).obj
        (forget (ModuleCat A)))

/-- 指定された集合的BK錐は同じ図式射と同じTot射の像を保つ。 -/
theorem normalizedBousfieldKanSetCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanSetCone X ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      normalizedBousfieldKanSetCone Y ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y) := by
  let H := (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
    (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj Y))
  have ht := normalizedLinearWeightHomEquiv_postcomp A bousfieldKanSetWeight
    (normalizedBousfieldKanConeRepresentative X)
    (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f)
  have hs := normalizedLinearWeightHomEquiv_postcomp A bousfieldKanSetWeight
    (normalizedBousfieldKanConeRepresentative Y)
    (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)
  exact ht.symm.trans ((congrArg (normalizedLinearWeightHomEquiv A bousfieldKanSetWeight H)
    (normalizedBousfieldKanConeRepresentative_dinaturality f)).trans hs)

/-- 指定Moore反転を前合成した同じ複体代表も双方向自然性を保つ。 -/
theorem reflectedBousfieldKanConeRepresentative_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedBousfieldKanConeRepresentative X ≫
        normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f =
      reflectedBousfieldKanConeRepresentative Y ≫
        normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y := by
  let r := (ComplexShape.embeddingDownNat.extendFunctor
    (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat A)).map
      (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
  change (r ≫ normalizedBousfieldKanConeRepresentative X) ≫ _ =
    (r ≫ normalizedBousfieldKanConeRepresentative Y) ≫ _
  simp only [Category.assoc]
  rw [normalizedBousfieldKanConeRepresentative_dinaturality]

/-- 同じ反転重みの集合的BK錐も全単体で双方向自然性を保つ。 -/
theorem reflectedBousfieldKanSetCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedBousfieldKanSetCone X ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      reflectedBousfieldKanSetCone Y ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y) := by
  let W := SimplicialObject.opFunctor.obj bousfieldKanSetWeight
  let H := (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
    (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj Y))
  have ht := normalizedLinearWeightHomEquiv_postcomp A W
    (reflectedBousfieldKanConeRepresentative X)
    (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f)
  have hs := normalizedLinearWeightHomEquiv_postcomp A W
    (reflectedBousfieldKanConeRepresentative Y)
    (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)
  exact ht.symm.trans ((congrArg (normalizedLinearWeightHomEquiv A W H)
    (reflectedBousfieldKanConeRepresentative_dinaturality A f)).trans hs)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

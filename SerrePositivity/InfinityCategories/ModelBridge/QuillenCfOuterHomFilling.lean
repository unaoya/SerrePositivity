module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UpperMissingCylinder
public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfRightLift
public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfLeftLift

/-!
概要：左右の元の cf Quillen 候補辺の Hom 射に沿って二つの未知写像を構成する。
方針：混合 Hom の Kan 性と、実際の候補辺による Hom 射の trivial Kan 性を代入。
規約：境界入力と可換条件は別途ホーンから構成する。Cartesian 性自体は未主張。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {Q : SSet.{u}}
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [ModelCategory C] [ModelCategory D] [SimplicialCategory C] [SimplicialCategory D]
  (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
  (adj : L ⊣ coherentEnrichedUnderlyingFunctor R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  [FixedSimplicialPushoutProduct SC.tensor]
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include SC in
/-- 元の右候補辺の後合成に沿う、空洞延長と境界固定の二段持ち上げ。 -/
lemma quillenCfRightHom_twoStageLift (A : Q.Subcomplex)
    (X : CofibrantFibrantObjects C) (Y : CofibrantFibrantObjects D)
    (f : (A : SSet) ⟶ ((quillenCfCollageBottom R).obj X ⟶[SSet]
      (quillenCfCollageBottom R).obj (quillenCfRightLiftObject R adj cofC Y)))
    (H₀ : (upperMissingCylinder A : SSet) ⟶
      ((quillenCfCollageBottom R).obj X ⟶[SSet] (quillenCfCollageTop R).obj Y))
    (h : f ≫ eHomWhiskerLeft SSet ((quillenCfCollageBottom R).obj X)
      (quillenCfRightLiftArrow R adj cofC Y) = upperMissingCylinderTopBoundary A ≫ H₀) :
    ∃ (H : Q ⊗ Δ[1] ⟶
        ((quillenCfCollageBottom R).obj X ⟶[SSet] (quillenCfCollageTop R).obj Y))
      (l : Q ⟶ ((quillenCfCollageBottom R).obj X ⟶[SSet]
        (quillenCfCollageBottom R).obj (quillenCfRightLiftObject R adj cofC Y))),
      (upperMissingCylinder A).ι ≫ H = H₀ ∧ A.ι ≫ l = f ∧
        l ≫ eHomWhiskerLeft SSet ((quillenCfCollageBottom R).obj X)
          (quillenCfRightLiftArrow R adj cofC Y) = SSet.ι₁ ≫ H := by
  have : KanComplex
      ((quillenCfCollageBottom R).obj X ⟶[SSet] (quillenCfCollageTop R).obj Y) :=
    quillenMixedHom_kanComplex adj SC X.obj Y.obj
  have := quillenCfRightLiftHom_trivialKanFibration R adj cofC SC X Y
  exact upperMissingCylinder_twoStageLift A _ f H₀ h


variable (fibD : MorphismProperty.FunctorialFactorizationData
  (trivialCofibrations D) (fibrations D))
  (e : EnrichedAdjunctionHomComposition R adj)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SD.tensor]
include e SC SD in
/-- 元の左候補辺の前合成に沿う、同じ二段持ち上げ。 -/
lemma quillenCfLeftHom_twoStageLift (A : Q.Subcomplex)
    (X : CofibrantFibrantObjects C) (Y : CofibrantFibrantObjects D)
    (f : (A : SSet) ⟶
      ((quillenCfCollageTop R).obj (quillenCfLeftLiftObject R adj fibD X) ⟶[SSet]
        (quillenCfCollageTop R).obj Y))
    (H₀ : (upperMissingCylinder A : SSet) ⟶
      ((quillenCfCollageBottom R).obj X ⟶[SSet] (quillenCfCollageTop R).obj Y))
    (h : f ≫ eHomWhiskerRight SSet (quillenCfLeftLiftArrow R adj fibD X)
      ((quillenCfCollageTop R).obj Y) = upperMissingCylinderTopBoundary A ≫ H₀) :
    ∃ (H : Q ⊗ Δ[1] ⟶
        ((quillenCfCollageBottom R).obj X ⟶[SSet] (quillenCfCollageTop R).obj Y))
      (l : Q ⟶ ((quillenCfCollageTop R).obj (quillenCfLeftLiftObject R adj fibD X) ⟶[SSet]
        (quillenCfCollageTop R).obj Y)),
      (upperMissingCylinder A).ι ≫ H = H₀ ∧ A.ι ≫ l = f ∧
        l ≫ eHomWhiskerRight SSet (quillenCfLeftLiftArrow R adj fibD X)
          ((quillenCfCollageTop R).obj Y) = SSet.ι₁ ≫ H := by
  have : KanComplex
      ((quillenCfCollageBottom R).obj X ⟶[SSet] (quillenCfCollageTop R).obj Y) :=
    quillenMixedHom_kanComplex adj SC X.obj Y.obj
  have := quillenCfLeftLiftHom_trivialKanFibration R adj fibD e SD X Y
  exact upperMissingCylinder_twoStageLift A _ f H₀ h

end
end SerrePositivity.InfinityCategories.HomotopyLimits

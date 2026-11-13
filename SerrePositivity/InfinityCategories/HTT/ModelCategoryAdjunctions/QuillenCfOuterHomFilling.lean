module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.UpperMissingCylinder
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfRightLift
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfLeftLift

/-!
概要：左右の元の cf Quillen 候補辺の Hom 射に沿って二つの未知写像を構成する。
方針：混合 Hom の Kan 性と、実際の候補辺による Hom 射の trivial Kan 性を代入。
規約：境界入力と可換条件は別途ホーンから構成する。Cartesian 性自体は未主張。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {Q : SSet.{u}}
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [ModelCategory C] [ModelCategory D] [SimplicialCategory C] [SimplicialCategory D]
  (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
  (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor]
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include SC in
/-- 元の右候補辺の後合成に沿う、空洞延長と境界固定の二段持ち上げ。 -/
lemma quillenCfRightHom_twoStageLift (A : Q.Subcomplex)
    (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)
    (f : (A : SSet) ⟶ ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet]
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC Y)))
    (H₀ : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder A : SSet) ⟶
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet] (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y))
    (h : f ≫ eHomWhiskerLeft SSet ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X)
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow R adj cofC Y) = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinderTopBoundary A ≫ H₀) :
    ∃ (H : Q ⊗ Δ[1] ⟶
        ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet] (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y))
      (l : Q ⟶ ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet]
        (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC Y))),
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder A).ι ≫ H = H₀ ∧ A.ι ≫ l = f ∧
        l ≫ eHomWhiskerLeft SSet ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X)
          (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow R adj cofC Y) = SSet.ι₁ ≫ H := by
  have : KanComplex
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet] (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y) :=
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenMixedHom_kanComplex adj SC X.obj Y.obj
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftHom_trivialKanFibration R adj cofC SC X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder_twoStageLift A _ f H₀ h


variable (fibD : MorphismProperty.FunctorialFactorizationData
  (trivialCofibrations D) (fibrations D))
  (e : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EnrichedAdjunctionHomComposition R adj)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]
include e SC SD in
/-- 元の左候補辺の前合成に沿う、同じ二段持ち上げ。 -/
lemma quillenCfLeftHom_twoStageLift (A : Q.Subcomplex)
    (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)
    (f : (A : SSet) ⟶
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD X) ⟶[SSet]
        (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y))
    (H₀ : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder A : SSet) ⟶
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet] (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y))
    (h : f ≫ eHomWhiskerRight SSet (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD X)
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y) = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinderTopBoundary A ≫ H₀) :
    ∃ (H : Q ⊗ Δ[1] ⟶
        ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet] (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y))
      (l : Q ⟶ ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD X) ⟶[SSet]
        (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y)),
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder A).ι ≫ H = H₀ ∧ A.ι ≫ l = f ∧
        l ≫ eHomWhiskerRight SSet (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD X)
          ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y) = SSet.ι₁ ≫ H := by
  have : KanComplex
      ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶[SSet] (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y) :=
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenMixedHom_kanComplex adj SC X.obj Y.obj
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftHom_trivialKanFibration R adj fibD e SD X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder_twoStageLift A _ f H₀ h

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions

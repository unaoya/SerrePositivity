module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanSetCone
public import SerrePositivity.HomologicalAlgebra.PointwiseTruncationGamma

/-!
概要：元の Tot の指定 BK 錐入力を、点ごとの切断・Dold–Kan 空間へ輸送する。
方針：図式圏の指定 Γ 比較と切断の mate を合成した自然同型を後合成する。
規約：頂点・線形 BK 重みを変えず、全単体作用素と添字射を保つ。
使われ方：HA 1.2.4、G10 の指定 native 錐への入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 点ごとの実 Hom 複体の smart 切断から得る単体集合の全図式。 -/
def pointwiseBousfieldKanHomSpaces (X : CosimplicialObject (Complex A)) :
    SimplexCategoryᵒᵖᵒᵖ ⥤ SimplicialObject (Type u) :=
  ((complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X)) ⋙
    (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat.{u} A) ⋙
    Abelian.DoldKan.Γ) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat.{u} A) (Type u)).obj
        (forget (ModuleCat.{u} A))

/-- 指定 BK 錐を、点ごとの Dold–Kan Hom 空間へ移した全自然変換。 -/
def pointwiseBousfieldKanSetCone (X : CosimplicialObject (Complex A)) :
    (bousfieldKanSetWeight ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (Type 0) (Type u)).obj
        uliftFunctor.{u,0}).flip ⟶ pointwiseBousfieldKanHomSpaces X :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖᵒᵖ (Type u)).map
    (normalizedBousfieldKanSetCone X) ≫
    Functor.whiskerRight
      ((pointwiseTruncationGammaIso SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A)).hom.app
        (bousfieldKanConeHomDiagram X))
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat.{u} A) (Type u)).obj
        (forget (ModuleCat.{u} A)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

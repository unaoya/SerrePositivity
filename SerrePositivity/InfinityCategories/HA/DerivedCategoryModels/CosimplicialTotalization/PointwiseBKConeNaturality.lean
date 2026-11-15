module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSetConeNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedPointwiseBousfieldKanCone

/-!
概要：同じΓ図式の係数自然性を、各点の実切断・Γと反転Homへ移す。
方針：既存pointwiseTruncationGammaIsoの全自然性とflip・反転の関手則を合成。
規約：IS-W2 D01の既存構成の係数移送・自然性則。全単体を保つ。
使われ方：HA 1.2.4、元の豊穣BK錐の全図式射への両立。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A]

/-- 各点の同じ切断・Γ・忘却を全係数複体図式に適用する。 -/
def pointwiseBKSetHomFunctor :
    CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ ⥤
      SimplexCategoryᵒᵖᵒᵖ ⥤ SSet.{u} :=
  complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ _ _).obj
      ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A) ⋙
        Abelian.DoldKan.Γ ⋙
        (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
          (forget (ModuleCat A)))

/-- 元の図式Γと点ごとのΓの指定比較の同じ忘却像。 -/
def pointwiseBKSetHomComparison
    (H : CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ) :=
  Functor.whiskerRight
    ((pointwiseTruncationGammaIso SimplexCategoryᵒᵖᵒᵖ (ModuleCat A)).hom.app H)
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
      (forget (ModuleCat A)))

/-- 同じ指定比較は、全係数複体射に自然。 -/
theorem pointwiseBKSetHomComparison_naturality
    {H H' : CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ} (f : H ⟶ H') :
    (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖᵒᵖ (Type u)).map
        ((bousfieldKanSetHomFunctor A).map f) ≫ pointwiseBKSetHomComparison A H' =
      pointwiseBKSetHomComparison A H ≫ (pointwiseBKSetHomFunctor A).map f := by
  have h := congrArg (fun η => Functor.whiskerRight η
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
      (forget (ModuleCat A))))
    ((pointwiseTruncationGammaIso SimplexCategoryᵒᵖᵒᵖ (ModuleCat A)).hom.naturality f)
  exact h

/-- 元の反転重みの点ごとのBK錐は、全図式射とTot射に両立する。 -/
theorem reversedWeightPointwiseBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reversedWeightPointwiseBousfieldKanCone X ≫
        (pointwiseBKSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      reversedWeightPointwiseBousfieldKanCone Y ≫
        (pointwiseBKSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y) := by
  let T := flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖᵒᵖ (Type u)
  let H := (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
    (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj Y))
  let t := normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f
  let s := normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y
  have ht := pointwiseBKSetHomComparison_naturality A t
  have hs := pointwiseBKSetHomComparison_naturality A s
  have h := congrArg T.map (reflectedBousfieldKanSetCone_dinaturality A f)
  simp only [Functor.map_comp] at h
  change (T.map (reflectedBousfieldKanSetCone X) ≫
      pointwiseBKSetHomComparison A (bousfieldKanConeHomDiagram X)) ≫ _ =
    (T.map (reflectedBousfieldKanSetCone Y) ≫
      pointwiseBKSetHomComparison A (bousfieldKanConeHomDiagram Y)) ≫ _
  calc
    _ = (T.map (reflectedBousfieldKanSetCone X) ≫
        T.map ((bousfieldKanSetHomFunctor A).map t)) ≫ pointwiseBKSetHomComparison A H := by
      rw [Category.assoc]
      erw [← ht]
      rw [Category.assoc]
    _ = (T.map (reflectedBousfieldKanSetCone Y) ≫
        T.map ((bousfieldKanSetHomFunctor A).map s)) ≫ pointwiseBKSetHomComparison A H := by
      rw [h]
    _ = _ := by
      rw [Category.assoc]
      erw [hs]
      rw [Category.assoc]
      rfl

/-- 再反転で元のBK重みへ戻しても、同じ全自然性が保たれる。 -/
theorem reflectedPointwiseBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedPointwiseBousfieldKanCone X ≫
        Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f))
          SimplicialObject.opFunctor =
      reflectedPointwiseBousfieldKanCone Y ≫
        Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y))
          SimplicialObject.opFunctor := by
  have h := congrArg (fun η => Functor.whiskerRight η SimplicialObject.opFunctor)
    (reversedWeightPointwiseBousfieldKanCone_dinaturality A f)
  simp only [Functor.whiskerRight_comp] at h
  unfold reflectedPointwiseBousfieldKanCone
  simp only [Category.assoc]
  erw [h]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

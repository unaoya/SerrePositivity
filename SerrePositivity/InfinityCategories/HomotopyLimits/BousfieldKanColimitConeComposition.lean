module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeEndPrecomposition

/-!
概要：構成済みの Kan coend の coherent な比較族を、普遍点と coslice の前合成で計算する。
方針：全 Hom の復元公式を一般の end の作用へ移し、実際の比較の uncurry を評価する。
規約：元の図式上の比較そのものの等式。構成済みの錐全体への延長はまだ主張しない。
使われ方：HTT 4.2.4.1 の coend の余錐と native な極限判定の幾何的接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- Hom パラメータへ、構成済みの Kan coend の普遍切断点を添える射。 -/
def bousfieldKanColimitPointParameter (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op ⟶
      bousfieldKanHolim
        (simplicialHomDiagram F.op (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙
          SSet.opFunctor) ⊗
        (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op :=
  (λ_ _).inv ≫ (kanReflectedBousfieldKanColimitHomPoint F ▷ _)

/-- 既存の coherent 錐の比較は、普遍点への end の前合成による実際の比較に一致する。 -/
lemma bousfieldKanCoherentConeComparison_of_point_action
    (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    bousfieldKanCoherentConeComparison F Y =
      (SSet.uliftFunctor.{u + 1, u}).map (bousfieldKanColimitPointParameter F Y) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (weightedConeEndPrecomposition F.op (Opposite.op Y)
            (Opposite.op (kanReflectedBousfieldKanColimitObject F))) ≫
          reflectedHomHolimConeComparison F.op (Opposite.op Y) := by
  have h := (kanReflectedBousfieldKanColimitHomComparison_of_point F Y).symm
  rw [← kanReflectedBousfieldKanEndPostcomposition_eq F
    (kanReflectedBousfieldKanColimitObject F) Y] at h
  rw [bousfieldKanCoherentConeComparison, h, Functor.map_comp, Category.assoc]
  rfl

/-- 既存の比較の全 Hom パラメータの評価は、普遍点から構成した coslice の族そのもの。 -/
lemma bousfieldKanCoherentConeComparison_uncurry
    (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    relativeFunctorUncurry (bousfieldKanCoherentConeComparison F Y) =
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ) ◁
        (SSet.uliftFunctor.{u + 1, u}).map (bousfieldKanColimitPointParameter F Y)) ≫
        (uliftTensorIso (nerve Iᵒᵖ)
          (bousfieldKanHolim
            (simplicialHomDiagram F.op
              (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor) ⊗
            (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op)).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            ((α_ (nerve Iᵒᵖ)
              (bousfieldKanHolim
                (simplicialHomDiagram F.op
                  (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor))
              (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op).inv ≫
              (bousfieldKanWeightedNerveEvaluation
                (simplicialHomDiagram F.op
                  (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor) ▷
                (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op)) ≫
            (uliftTensorIso _ _).hom ≫
              weightedCoslicePrecompositionFamily F.op (Opposite.op Y)
                (Opposite.op (kanReflectedBousfieldKanColimitObject F)) := by
  rw [bousfieldKanCoherentConeComparison_of_point_action, relativeFunctorUncurry_parameter,
    reflectedHomHolimConeComparison_precomposition_uncurry,
    weightedCosliceEndPrecompositionEvaluation_eq_family]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits

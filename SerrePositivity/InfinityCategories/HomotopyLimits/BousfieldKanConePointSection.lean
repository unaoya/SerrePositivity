module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConePointSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanColimitConeComposition

/-!
概要：Kan coend の coherent 錐の切断を、end の普遍点の weighted な評価へ戻す。
方針：固定頂点の錐と切断の全単射を計算し、coend の普遍点の照合式を使う。
規約：頂点の等式による移送を含む実際の切断そのものの等式。
使われ方：coend の錐全体の Hom の族を既存の Hom 比較へ制限する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- coend の反対錐の正規化した coslice 切断は、その普遍点の評価に等しい。 -/
lemma bousfieldKanCoherentOppositeCone_cosliceSection (F : I ⥤ KanObject.{u}) :
    coherentConeCosliceSection (bousfieldKanCoherentOppositeCone F) ≫
        eqToHom (congrArg (fun w ↦ sliceUnder (SSet.yonedaEquiv.symm w))
          (bousfieldKanCoherentOppositeCone_vertex F)) =
      inv (fst ((SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ))
        (Δ[0] : SSet.{u + 1})) ≫
          relativeFunctorUncurry (SSet.yonedaEquiv.symm (bousfieldKanCoherentConePoint F)) :=
  fixedVertexConeSpaceEquiv_cosliceSection _ _ _
    (bousfieldKanCoherentOppositeCone_vertex F)

/-- coend の end の普遍点を、持ち上げた切断の零単体として表示する射。 -/
def bousfieldKanLiftedEndPoint (F : I ⥤ KanObject.{u}) :
    (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (bousfieldKanHolim
        (simplicialHomDiagram F.op
          (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)) :=
  SSet.yonedaEquiv.symm (ULift.up
    ((kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋0⦌) PUnit.unit))

/-- coend の切断点の Yoneda 表示は、end の普遍点と既存の比較の合成。 -/
lemma bousfieldKanCoherentConePoint_yoneda (F : I ⥤ KanObject.{u}) :
    SSet.yonedaEquiv.symm (bousfieldKanCoherentConePoint F) =
      bousfieldKanLiftedEndPoint F ≫ reflectedHomHolimConeComparison F.op
        (Opposite.op (kanReflectedBousfieldKanColimitObject F)) := by
  rw [bousfieldKanCoherentConePoint_of_end_point, bousfieldKanLiftedEndPoint,
    SSet.yonedaEquiv_symm_comp]

/-- 普遍点の weighted nerve での実際の評価。 -/
def bousfieldKanConeWeightedPointSection (F : I ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (weightedNerve (simplicialHomDiagram F.op
          (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)) :=
  inv (fst _ (Δ[0] : SSet.{u + 1})) ≫ (_ ◁ bousfieldKanLiftedEndPoint F) ≫
    (uliftTensorIso _ _).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (bousfieldKanWeightedNerveEvaluation
        (simplicialHomDiagram F.op
          (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor))

/-- 錐の正規化した切断は、普遍点の weighted な切断と coslice 比較の合成。 -/
lemma bousfieldKanCoherentOppositeCone_cosliceSection_weighted (F : I ⥤ KanObject.{u}) :
    coherentConeCosliceSection (bousfieldKanCoherentOppositeCone F) ≫
        eqToHom (congrArg (fun w ↦ sliceUnder (SSet.yonedaEquiv.symm w))
          (bousfieldKanCoherentOppositeCone_vertex F)) =
      bousfieldKanConeWeightedPointSection F ≫ weightedCosliceComparison F.op
        (Opposite.op (kanReflectedBousfieldKanColimitObject F)) := by
  erw [bousfieldKanCoherentOppositeCone_cosliceSection, bousfieldKanCoherentConePoint_yoneda,
    relativeFunctorUncurry_parameter, reflectedHomHolimConeComparison_uncurry]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits

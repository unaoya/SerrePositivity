module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeEndPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanColimitEnrichedComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedWeightedHomCoefficients

/-!
概要：一般の Hom 図式の end の前合成を、Kan coend の既存の豊穣後合成と同定する。
方針：図式の等式による移送を成分評価で除き、反対圏の合成の二重交換を消去する。
規約：全 Hom パラメータでの射の等式。余錐の普遍性は仮定しない。
使われ方：HTT 4.2.4.1 の Kan coend 比較と実際の coslice の族の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- Kan の反対圏内の前合成は、元の内部 Hom の後合成そのもの。 -/
lemma kanReflectedHomPrecompositionDiagram_app (F : I ⥤ KanObject.{u})
    (Y Z : KanObject.{u}) (i : Iᵒᵖ) :
    (reflectedHomPrecompositionDiagram F.op (Opposite.op Z) (Opposite.op Y)).app i =
      (Functor.Monoidal.μIso SSet.opFunctor ((ihom (F.obj i.unop).obj).obj Y.obj)
        ((ihom Y.obj).obj Z.obj)).hom ≫
          SSet.opFunctor.map (MonoidalClosed.comp (F.obj i.unop).obj Y.obj Z.obj) := by
  rfl

/-- Kan coend の係数図式の同定による end の同型は、各係数の評価を変えない。 -/
lemma kanReflectedBousfieldKanEndIso_evaluation (F : I ⥤ KanObject.{u})
    (Y : KanObject.{u}) (i : Iᵒᵖ) :
    (bousfieldKanWeight Iᵒᵖ).obj i ◁ (kanReflectedBousfieldKanEndIso F Y).hom ≫
        uncurry (weightedSectionsπ (bousfieldKanWeight Iᵒᵖ)
          (simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) i) =
      uncurry (weightedSectionsπ (bousfieldKanWeight Iᵒᵖ)
        (weightedColimitHomDiagram (F ⋙ kanObjectForget) Y.obj ⋙ SSet.opFunctor) i) := by
  have h := weightedSections_diagram_eq_evaluation (bousfieldKanWeight Iᵒᵖ)
    (congrArg (fun D ↦ D ⋙ SSet.opFunctor) (kanBousfieldKanColimitHomDiagram_eq F Y)) i
  convert h using 1 <;> rfl

/-- 既存の Kan end の後合成は、一般の Hom 図式の end の前合成と厳密に一致する。 -/
lemma kanReflectedBousfieldKanEndPostcomposition_eq (F : I ⥤ KanObject.{u})
    (Y Z : KanObject.{u}) :
    weightedConeEndPrecomposition F.op (Opposite.op Z) (Opposite.op Y) =
      kanReflectedBousfieldKanEndPostcomposition F Y Z := by
  apply weightedSections_hom_ext
  intro i
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left]
  apply (cancel_epi ((bousfieldKanWeight Iᵒᵖ).obj i ◁
    ((kanReflectedBousfieldKanEndIso F Y).hom ▷ (SimplicialCategory.sHom Y Z).op))).mp
  rw [weightedConeEndPrecomposition, weightedSectionsParameterMap_evaluation,
    kanReflectedHomPrecompositionDiagram_app]
  dsimp only [kanReflectedBousfieldKanEndPostcomposition]
  conv_rhs =>
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← Category.assoc,
      ← comp_whiskerRight, Iso.hom_inv_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [kanReflectedBousfieldKanEndIso_evaluation]
  erw [associator_inv_naturality_middle_assoc]
  erw [← comp_whiskerRight_assoc]
  rw [kanReflectedBousfieldKanEndIso_evaluation]
  exact (reflectedWeightedHomPostcomposition_evaluation (bousfieldKanWeight Iᵒᵖ)
    (F ⋙ kanObjectForget) Y.obj Z.obj i).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits

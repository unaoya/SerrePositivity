module

public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedSectionsOpposite
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeKanHomotopy

/-!
概要：反転した重みの coend から、coherent 錐に適合する反転係数の end を構成する。
方針：coend の Hom 同型と end の反転同型を合成し、Kan 置換を前合成する。
規約：係数の反転を任意の逆の選択で置き換えない。native な普遍性は別途証明する。
使われ方：HTT 4.2.4.1、γ3c の coherent な余錐と反転 Hom の切断模型の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 反転した重みの coend の反転 Hom は、元の重み・反転係数の end に同型。 -/
def reflectedWeightedColimitHomIso (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    ((ihom (weightedColimit (W ⋙ SSet.opFunctor) F)).obj Y).op ≅
      weightedSections W (weightedColimitHomDiagram F Y ⋙ SSet.opFunctor) :=
  SSet.opFunctor.mapIso (weightedColimitHomIso (W ⋙ SSet.opFunctor) F Y) ≪≫
    weightedSectionsReflectedIso W (weightedColimitHomDiagram F Y)

/-- 反転重みの coend の Hom 同型は終域に自然。 -/
lemma reflectedWeightedColimitHomIso_naturality (W : Iᵒᵖ ⥤ SSet.{u})
    (F : I ⥤ SSet.{u}) {Y Z : SSet.{u}} (f : Y ⟶ Z) :
    SSet.opFunctor.map ((ihom (weightedColimit (W ⋙ SSet.opFunctor) F)).map f) ≫
        (reflectedWeightedColimitHomIso W F Z).hom =
      (reflectedWeightedColimitHomIso W F Y).hom ≫
        weightedSectionsMap W (Functor.whiskerRight (weightedColimitHomDiagramMap F f)
          SSet.opFunctor) := by
  change SSet.opFunctor.map ((ihom (weightedColimit (W ⋙ SSet.opFunctor) F)).map f) ≫
      SSet.opFunctor.map (weightedColimitHomComparison (W ⋙ SSet.opFunctor) F Z) ≫
        (weightedSectionsReflectedIso W (weightedColimitHomDiagram F Z)).hom =
    (SSet.opFunctor.map (weightedColimitHomComparison (W ⋙ SSet.opFunctor) F Y) ≫
      (weightedSectionsReflectedIso W (weightedColimitHomDiagram F Y)).hom) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, weightedColimitHomComparison_naturality,
    Functor.map_comp, Category.assoc, weightedSectionsReflectedIso_naturality,
    Category.assoc]

/-- coherent な錐の反転係数に適合する Bousfield–Kan coend。 -/
def reflectedBousfieldKanColimit (F : I ⥤ SSet.{u}) : SSet.{u} :=
  weightedColimit (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) F

/-- 反転した重みの coend の実際の Kan 置換。 -/
def kanReflectedBousfieldKanColimitObject (F : I ⥤ KanObject.{u}) : KanObject.{u} :=
  anodyneKanObject (reflectedBousfieldKanColimit (F ⋙ kanObjectForget))

/-- 置換前の反転 Hom と、既存の反転した豊穣 Hom の end の厳密な同型。 -/
def kanReflectedBousfieldKanColimitUnderlyingHomIso (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    ((ihom (reflectedBousfieldKanColimit (F ⋙ kanObjectForget))).obj Y.obj).op ≅
      bousfieldKanHolim (simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) :=
  reflectedWeightedColimitHomIso (bousfieldKanWeight Iᵒᵖ) (F ⋙ kanObjectForget) Y.obj ≪≫
    eqToIso (congrArg (fun D ↦ bousfieldKanHolim (D ⋙ SSet.opFunctor))
      (kanBousfieldKanColimitHomDiagram_eq F Y))

/-- Kan 置換後の反転 Hom から、coherent な錐に適合する実際の end への比較射。 -/
def kanReflectedBousfieldKanColimitHomComparison (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op ⟶
      bousfieldKanHolim (simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) :=
  SSet.opFunctor.map ((pre
    (anodyneKanObjectUnit (reflectedBousfieldKanColimit (F ⋙ kanObjectForget)))).app Y.obj) ≫
      (kanReflectedBousfieldKanColimitUnderlyingHomIso F Y).hom

/-- coherent 錐の係数に直接入る反転 Hom の比較射はホモトピー同値。 -/
lemma kanReflectedBousfieldKanColimitHomComparison_homotopyEquivalence
    (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    IsSimplicialHomotopyEquivalence (kanReflectedBousfieldKanColimitHomComparison F Y) := by
  have : ∀ i, KanComplex
      ((simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom (F.obj i.unop) Y).op)
  have := bousfieldKanHolim_kanComplex
    (simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor)
  exact (oppositeKanHomotopyEquivalence
    (homotopyEquivalence_pre_of_anodyne _ (anodyneKanObjectUnit_anodyne _) Y.obj)).comp
      (homotopyEquivalence_of_isIso (kanReflectedBousfieldKanColimitUnderlyingHomIso F Y).hom)

end
end SerrePositivity.InfinityCategories.HomotopyLimits

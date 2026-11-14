module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedSectionsOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 反転した重みの coend の反転 Hom は、元の重み・反転係数の end に同型。 -/
def reflectedWeightedColimitHomIso (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F)).obj Y).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y ⋙ SSet.opFunctor) :=
  SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomIso (W ⋙ SSet.opFunctor) F Y) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)

/-- 反転重みの coend の Hom 同型は終域に自然。 -/
lemma reflectedWeightedColimitHomIso_naturality (W : Iᵒᵖ ⥤ SSet.{u})
    (F : I ⥤ SSet.{u}) {Y Z : SSet.{u}} (f : Y ⟶ Z) :
    SSet.opFunctor.map ((ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F)).map f) ≫
        (reflectedWeightedColimitHomIso W F Z).hom =
      (reflectedWeightedColimitHomIso W F Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagramMap F f)
          SSet.opFunctor) := by
  change SSet.opFunctor.map ((ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F)).map f) ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison (W ⋙ SSet.opFunctor) F Z) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z)).hom =
    (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison (W ⋙ SSet.opFunctor) F Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)).hom) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison_naturality,
    Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso_naturality,
    Category.assoc]

/-- coherent な錐の反転係数に適合する Bousfield–Kan coend。 -/
def reflectedBousfieldKanColimit (F : I ⥤ SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) F

/-- 反転した重みの coend の実際の Kan 置換。 -/
def kanReflectedBousfieldKanColimitObject (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject (reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))

/-- 置換前の反転 Hom と、既存の反転した豊穣 Hom の end の厳密な同型。 -/
def kanReflectedBousfieldKanColimitUnderlyingHomIso (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    ((ihom (reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))).obj Y.obj).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) :=
  reflectedWeightedColimitHomIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) Y.obj ≪≫
    eqToIso (congrArg (fun D ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (D ⋙ SSet.opFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanBousfieldKanColimitHomDiagram_eq F Y))

/-- Kan 置換後の反転 Hom から、coherent な錐に適合する実際の end への比較射。 -/
def kanReflectedBousfieldKanColimitHomComparison (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) :=
  SSet.opFunctor.map ((pre
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)))).app Y.obj) ≫
      (kanReflectedBousfieldKanColimitUnderlyingHomIso F Y).hom

/-- coherent 錐の係数に直接入る反転 Hom の比較射はホモトピー同値。 -/
lemma kanReflectedBousfieldKanColimitHomComparison_homotopyEquivalence
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (kanReflectedBousfieldKanColimitHomComparison F Y) := by
  have : ∀ i, KanComplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom (F.obj i.unop) Y).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne _) Y.obj)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (kanReflectedBousfieldKanColimitUnderlyingHomIso F Y).hom)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

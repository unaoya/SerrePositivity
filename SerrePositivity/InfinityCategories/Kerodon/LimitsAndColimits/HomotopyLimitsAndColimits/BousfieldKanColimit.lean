module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimitHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement

/-!
概要：一般の小図式の Bousfield–Kan coend と、その Kan 置換の写像空間を構成する。
方針：Iᵒᵖ 上の既存の重みを用い、coend と end の内部 Hom 同型を特殊化する。
規約：実際の対象と Hom 比較を公開する。native な coherent 余錐と余極限性は別の証明対象。
使われ方：HTT 4.2.4.1、γ3c の一般の余極限候補を coherent な普遍性へ接続する入力。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 任意の小図式の反変 Bousfield–Kan 重みによる coend。 -/
def bousfieldKanColimit (F : I ⥤ SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F

/-- Bousfield–Kan coend の内部 Hom は反変 Hom 図式の既存の end に同型。 -/
def bousfieldKanColimitHomIso (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    (ihom (bousfieldKanColimit F)).obj Y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F Y

/-- 任意の小さい Kan 値図式の coend を実際に Kan 置換した対象。 -/
def kanBousfieldKanColimitObject (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject (bousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))

/-- 反変 Hom 係数は既存の反対圏の豊穣 Hom 図式と一致する。 -/
lemma kanBousfieldKanColimitHomDiagram_eq (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) Y.obj =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectOppositeHomFunctor_eq Y]
  rfl

/-- coend の Hom 同型を、Kan 値図式の反変豊穣 Hom の end に合わせる。 -/
def kanBousfieldKanColimitUnderlyingHomIso (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (ihom (bousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))).obj Y.obj ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y)) :=
  bousfieldKanColimitHomIso (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) Y.obj ≪≫
    eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (kanBousfieldKanColimitHomDiagram_eq F Y))

/-- Kan 置換後の Hom から一般の反変豊穣 Hom の end への実際の比較。 -/
def kanBousfieldKanColimitHomComparison (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    SimplicialCategory.sHom (kanBousfieldKanColimitObject F) Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y)) :=
  (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (bousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)))).app Y.obj ≫
    (kanBousfieldKanColimitUnderlyingHomIso F Y).hom

/-- Kan 置換後の写像空間は、一般の小図式の反変 Hom の end とホモトピー同値。 -/
lemma kanBousfieldKanColimitHomComparison_homotopyEquivalence
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (kanBousfieldKanColimitHomComparison F Y) := by
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y)).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom (F.obj i.unop) Y))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne _) Y.obj).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (kanBousfieldKanColimitUnderlyingHomIso F Y).hom)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

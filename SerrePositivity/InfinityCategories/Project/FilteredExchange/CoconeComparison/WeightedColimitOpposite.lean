module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：重み付き coend の反転は重みと係数の同時反転の coend に同型。
方針：直積の反転同型を multicoequalizer の図式全体に使う。
規約：係数と重みの両方を反転する。Kan 性は不要。
使われ方：反転重みの Bousfield–Kan augmentation の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitOpposite

variable {I : Type u} [SmallCategory I]
local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：重み付き coend の multispan を反転すると同時反転の図式に同型。
方針：全成分で直積の反転同型を使う。
規約：二つの coend の関係射を保持する。使われ方：coend の反転同型。 -/
def oppositeWeightedColimitDiagramIso (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    (multispanIndexCoend (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitDiagram W F)).multispan ⋙ SSet.opFunctor ≅
      (multispanIndexCoend (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitDiagram (W ⋙ SSet.opFunctor)
        (F ⋙ SSet.opFunctor))).multispan := by
  refine NatIso.ofComponents ?_ ?_
  · intro j
    cases j with
    | left f => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeTensorIso (F.obj f.left) (W.obj (Opposite.op f.right))
    | right i => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeTensorIso (F.obj i) (W.obj (Opposite.op i))
  · rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl

/-- 概要：単体順序の反転は重み付き coend と同型を介して交換する。
方針：反転の余極限保存と multispan の同型を合成する。
規約：添字圏は変更しない。使われ方：反転重みの模型の比較。 -/
def weightedColimitOppositeIso (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F).op ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) (F ⋙ SSet.opFunctor) :=
  preservesColimitIso SSet.opFunctor
    (multispanIndexCoend (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitDiagram W F)).multispan ≪≫
      HasColimit.isoOfNatIso (oppositeWeightedColimitDiagramIso W F)

/-- 概要：coend の反転同型は元の普遍脚を同時反転した普遍脚に送る。
方針：余極限保存同型と図式同型の脚の公式を合成する。
規約：全ての単体での射の等式。使われ方：augmentation との整合。 -/
lemma weightedColimitOppositeIso_ι (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (i : I) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i) ≫ (weightedColimitOppositeIso W F).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeTensorIso (F.obj i) (W.obj (Opposite.op i))).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (W ⋙ SSet.opFunctor) (F ⋙ SSet.opFunctor) i := by
  change SSet.opFunctor.map (colimit.ι _ (.right i)) ≫ (preservesColimitIso _ _).hom ≫
    (HasColimit.isoOfNatIso (oppositeWeightedColimitDiagramIso W F)).hom = _
  rw [← Category.assoc, ι_preservesColimitIso_hom, HasColimit.ι_isoOfNatIso_hom]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitOpposite

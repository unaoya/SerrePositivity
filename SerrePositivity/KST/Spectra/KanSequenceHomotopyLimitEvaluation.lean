module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit
public import SerrePositivity.KST.Spectra.MappingOmegaSequence
public import SerrePositivity.KST.Spectra.PointedWeightedConeCompatibility
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry

/-!
概要：段ごとの homotopy end の射影を、重みからの内部 Hom 列への実際の厳密な射にする。
方針：end の loop 交換を射影で計算し、逆順の内部 Hom 交換の逆射を使う。
規約：射影の構造可換性を証明する。使われ方：小図式の実際の enriched end の錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
namespace SerrePositivity.KST.Spectra

namespace PointedWeightedEnd

/-- loop と end の逆向きの交換を、元の end の射影で計算する。 -/
@[reassoc]
lemma cotensorIso_inv_π {I : Type u} [SmallCategory I] (A : PointedSimplicialSet.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) (i : I) :
    (cotensorIso A W D).inv ≫ (ihom A).map (end_.π (diagram W D) i) =
      end_.π (diagram W (D ⋙ ihom A)) i ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (PointedObject.adjoin (W.obj i)) (D.obj i)).inv := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (PointedObject.adjoin (W.obj i))
    (D.obj i)).hom).mp
  rw [Category.assoc, ← cotensorIso_π, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end PointedWeightedEnd
namespace KanSequence

variable {I : Type u} [SmallCategory I]

/-- homotopy end の各段を重みの内部 Hom へ評価する点つき射。 -/
def homotopyLimitEvaluationApp (D : I ⥤ KanSequence.{u}) (i : I) (n : ℕ) :
    ((homotopyLimit D).level n).space ⟶
      ((mapping (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)) (D.obj i)).level n).space :=
  end_.π (PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n)) i

/-- 各段の end の射影は実際の随伴構造射と可換。 -/
lemma homotopyLimitEvaluationApp_adjoint (D : I ⥤ KanSequence.{u}) (i : I) (n : ℕ) :
    homotopyLimitEvaluationApp D i n ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _
          ((mapping (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)) (D.obj i)).sigma n) =
      homotopyLimitAdjoint D n ≫
        (ihom PointedSimplicialSet.circle.{u}).map (homotopyLimitEvaluationApp D i (n + 1)) := by
  rw [mapping_adjoint]
  dsimp only [homotopyLimitAdjoint, homotopyLimitEvaluationApp]
  rw [Category.assoc, PointedWeightedEnd.cotensorIso_inv_π]
  conv_rhs => rw [← Category.assoc, PointedWeightedEnd.map_π]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv]
  rfl

/-- homotopy end から重みの内部 Hom 列への実際の厳密な射影。 -/
def homotopyLimitEvaluation (D : I ⥤ KanSequence.{u}) (i : I) :
    Hom (homotopyLimit D)
      (mapping (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)) (D.obj i)) where
  app := homotopyLimitEvaluationApp D i
  comm n := by
    apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _).injective
    change curry (PointedSimplicialSet.circle.{u} ◁ homotopyLimitEvaluationApp D i n ≫
        (mapping (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)) (D.obj i)).sigma n) =
      curry ((homotopyLimit D).sigma n ≫ homotopyLimitEvaluationApp D i (n + 1))
    rw [curry_natural_left, curry_natural_right]
    change _ = curry (uncurry (homotopyLimitAdjoint D n)) ≫ _
    rw [curry_uncurry]
    exact homotopyLimitEvaluationApp_adjoint D i n

end KanSequence
end SerrePositivity.KST.Spectra

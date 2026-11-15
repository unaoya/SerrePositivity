module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanDoubleOppositeWeight
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSectionsDoubleOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：指定したBK endの二重反対への移送は同型であり、元の錐比較を保つ。
方針：既存の重みの前合成の逆則とendの再添字を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の実係数の比較。
規約：重みの射は元のweightPostそのもの。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel
variable (I : Type u) [SmallCategory I]

/-- 指定した重みの再添字による前合成に、その指定逆の前合成を合わせる。 -/
def bousfieldKanOpOpWeightSectionsIso (H : I ⥤ SSet.{u}) :
    weightedSections (opOp I ⋙ bousfieldKanWeight Iᵒᵖᵒᵖ) H ≅ bousfieldKanHolim H where
  hom := weightedSectionsPre (bousfieldKanOpOpWeightIso I).hom H
  inv := weightedSectionsPre (bousfieldKanOpOpWeightIso I).inv H
  hom_inv_id := by rw [← weightedSectionsPre_comp, Iso.inv_hom_id, weightedSectionsPre_id]
  inv_hom_id := by
    rw [← weightedSectionsPre_comp, Iso.hom_inv_id, weightedSectionsPre_id]
    rfl

/-- 同じendを標準の二重反対の逆へ再添字する指定同型。 -/
def bousfieldKanOpOpIso (H : Iᵒᵖᵒᵖ ⥤ SSet.{u}) :
    bousfieldKanHolim H ≅ bousfieldKanHolim (opOp I ⋙ H) :=
  weightedSectionsOpOpIso I (bousfieldKanWeight Iᵒᵖᵒᵖ) H ≪≫
    bousfieldKanOpOpWeightSectionsIso I (opOp I ⋙ H)

/-- 同じ再添字は指定錐比較を、そのまま制限した錐比較へ送る。 -/
lemma bousfieldKanOpOpIso_cone {H : Iᵒᵖᵒᵖ ⥤ SSet.{u}} (c : Cone H) :
    bousfieldKanConeComparison c ≫ (bousfieldKanOpOpIso I H).hom =
      bousfieldKanConeComparison (c.whisker (opOp I)) := by
  change weightedConeComparison _ c ≫ (_ ≫ _) = _
  rw [← Category.assoc, weightedSectionsOpOpIso_cone]
  exact weightedConeComparison_pre (bousfieldKanOpOpWeightIso I).hom _

end SerrePositivity.DiagramModel

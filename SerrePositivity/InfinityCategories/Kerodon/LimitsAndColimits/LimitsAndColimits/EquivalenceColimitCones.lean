module

public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.F1B.Equivalences.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
同値による余極限錐の保存と反映。Kerodon 7.1.4.12（Tag 02JZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.InfinityCategories.F2

/-- 同じ元の関手が同値なら、元の任意の全余錐の余極限性を保存・反映する。 -/
@[kerodon 02JZ]
lemma equivalence_isColimitCone_iff {K C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    {G : C ⟶ E} (hG : IsQCatEquivalence G) {D : K ⟶ C} (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone G c) :=
  (SerrePositivity.InfinityCategories.F1B.isColimitCone_iff_reverseCone c).trans
    (((SerrePositivity.InfinityCategories.F1B.isQCatEquivalence_op hG).isLimitCone_iff (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c)).trans
      (isLimitCone_reverse_postcomp_iff c G))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

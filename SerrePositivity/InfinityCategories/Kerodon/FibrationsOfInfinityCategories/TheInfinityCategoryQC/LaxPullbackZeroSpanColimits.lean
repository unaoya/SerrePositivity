module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackColimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ExactFunctorSpanCospanPreservation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackZeroProjections
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpecifiedCofiberSpan

/-!
概要：零対象への第二枝を持つ lax pullback の指定 span の余極限。
方針：両射影の零保存で入力の安定圏の存在を使い、完全性から像の保存を導く。
規約：lax pullback の安定性や全有限余極限を仮定しない。
使われ方：cofiber の存在と射影の完全性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable A] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B] (p : A ⟶ C) (q : B ⟶ C)
variable [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor p] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q]

/-- 概要：第二枝の終点が零対象である span の両入力は余極限を持つ。
方針：元の二関手の完全性から両射影の零保存を使い、安定圏の零枝の存在を適用する。
規約：入力の二つの span は元の射影による図式。
使われ方：lax pullback の零角四角形の成分判定の存在条件。 -/
lemma laxPullback_span_input_colimits_of_zero_second
    (r : (horn 2 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((horn₂₀.ι₀₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q) := by
  constructor
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_span_of_zero_second
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌)
      ((horn₂₀.ι₀₂ ≫ r).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackFst_preservesZero p q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q)) _ hz
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_span_of_zero_second
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q).app (Opposite.op ⦋0⦌)
      ((horn₂₀.ι₀₂ ≫ r).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackSnd_preservesZero p q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q)) _ hz

variable [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]

/-- 概要：第二枝が零対象へ向かう指定 span は lax pullback で余極限を持つ。
方針：入力の安定性による存在と元の完全関手の span 余極限保存を使う。
規約：元の指定された span 全体を固定する。
使われ方：cofiber 四角形の構成。 -/
lemma hasColimit_laxPullback_span_of_zero_second
    (r : (horn 2 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((horn₂₀.ι₀₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit r := by
  obtain ⟨ha, hb⟩ := laxPullback_span_input_colimits_of_zero_second p q r hz
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_laxPullback_of_components p q r ha hb
    (fun c hc ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exactFunctor_preserves_span_colimit p c hc)
    (fun c hc ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exactFunctor_preserves_span_colimit q c hc)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

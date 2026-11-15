module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanWeightLifting
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
概要：実際のBK重みの射影的な左持ち上げ条件。
方針：既存BK endから移送した持ち上げを、空図式からの射の持ち上げに渡す。
規約：SSetの完全なモデル構造を使わず、係数ごとの自明Kan fibrationに対して述べる。
使われ方：HTT 4.2.4.4のRR02(a)、複体側の実現随伴への直接移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.DiagramModel
variable (K : Type u) [SmallCategory K]

/-- BK重みは係数ごとの自明Kan fibrationに対する射影的左持ち上げ条件を満たす。 -/
lemma bousfieldKanWeight_projective_llp :
    (trivialKanFibrations.functorCategory K).llp (initial.to (bousfieldKanWeight K)) := by
  intro F G p hp
  have : ∀ k, TrivialKanFibration (p.app k) := fun k => ⟨hp k⟩
  constructor
  intro a b sq
  obtain ⟨l, hl⟩ := exists_bousfieldKanWeight_lift p b
  exact CommSq.HasLift.mk' {
    l := l
    fac_left := initial.hom_ext _ _
    fac_right := hl }

end SerrePositivity.DiagramModel

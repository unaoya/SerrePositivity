module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafRelativeCechEvaluation
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafPushoutCocones

/-!
概要：各点で全射な集合値前層の相対 Čech 増大は、同じ空間値前層の余極限余錐になる。
方針：元の全余錐の評価の式と既存の点ごとの余極限判定を使う。
規約：HTT 5.1.2.3、Kerodon §7.6（Tag 03E8）の点ごとの判定の適用。
使われ方：S8 の像への全射の Čech 解消。元の頂点と増大の全ての脚を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 元の同じ増大の全余錐を評価して、実際の空間値前層の余極限性を得る。 -/
lemma presheafRelativeCechCocone_isColimit (f : P ⟶ Q)
    (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) :
    IsColimitCone (discretePresheafCocone (relativeCechCocone f)) := by
  apply isColimitCone_of_pointwise
  rintro ⟨s⟩
  obtain ⟨U, rfl⟩ := ComposableArrows.mk₀_surjective s
  apply (isColimitCone_iff_of_cocone_val_eq _ _
    (discretePresheafCocone_evaluate_val (relativeCechCocone f) U)).mpr
  rw [discreteSpaceCocone]
  apply (coherentCoconeOfDiagramEq_isColimit_iff
    (strictCoherentDiagram_eq_kanDiagram
      ((relativeCechDiagram f ⋙ (evaluation Cᵒᵖ (Type u)).obj U) ⋙ setsToKan)) _).mpr
  exact presheafRelativeCechEvaluation_isColimit f hf U.unop

end SerrePositivity.InfinityCategories.Sheaves

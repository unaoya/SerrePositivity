module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Diagram.SpanCofibrations
public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen

/-! # Cofibration legs for projective spans in independent universes

An index category in the presentability universe may be equivalent to the
ordinary walking span. Reindex its actual projective cofibrancy, retaining
the original target category and its Hom universe.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.ProjectiveSpan
variable (K : Type w) [SmallCategory K] (e : K ≌ WalkingSpan)
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

lemma legs_cofibrations (D : K ⥤ C)
    (hD : let := Projective.modelCategory K I J; IsCofibrant D) :
    cofibrations C (D.map (e.inverse.map WalkingSpan.Hom.fst)) ∧
      cofibrations C (D.map (e.inverse.map WalkingSpan.Hom.snd)) := by
  let := Projective.modelCategory K I J
  have := hD
  have hc : cofibrations (K ⥤ C) (initial.to D) := mem_cofibrations _
  rw [← trivialFibrations_llp (K ⥤ C)] at hc
  have hi : ((trivialFibrations C).functorCategory K).llp (initial.to D) := by
    intro A B p hp
    exact hc p ⟨fun k => (hp k).1, fun k => (hp k).2⟩
  have h := ProjectiveReindexing.llp_map e (trivialFibrations C) (initial.to D) hi
  let F := (e.congrLeft (E := C)).functor
  have hP : IsInitial (F.obj (⊥_ (K ⥤ C))) := initialIsInitial.isInitialObj F _
  exact ⟨SpanCofibrations.fst_cofibration _ hP h,
    SpanCofibrations.snd_cofibration _ hP h⟩

end SerrePositivity.DiagramModel.ProjectiveSpan

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.8.12" (partial := direction) "仮定：walking span と同値な小さい K、Mathlib locally presentable な cofibrantly generated 抽象モデル圏（HTT の必要条件と一致）。結論：実際の projectively cofibrant diagram から root X の cofibrant 性と二つの legs の cofibration 性を得る。三条件から projective cofibrancy を構成する逆方向の型はない。"] _root_.SerrePositivity.DiagramModel.ProjectiveSpan.legs_cofibrations

module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveReindexing
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-! # Cofibration legs of projectively cofibrant spans

Projective cofibrancy is used as an actual lifting property. A test diagram
with an identity at the center and one arbitrary trivial fibration at a leaf
extracts the required lifting property of either leg. No diagram model or
presentability hypothesis is needed for this lemma.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.SpanCofibrations
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {P D : WalkingSpan ⥤ C} (i : P ⟶ D) (hP : IsInitial P)
  (hi : ((trivialFibrations C).functorCategory WalkingSpan).llp i)

include hP hi in
lemma fst_cofibration : cofibrations C (D.map WalkingSpan.Hom.fst) := by
  rw [← trivialFibrations_llp C]
  intro X Y p hp
  constructor
  intro a b sq
  let U := span (𝟙 X) (terminal.from X)
  let V := span p (terminal.from X)
  let q : U ⟶ V := spanHomMk (𝟙 X) p (𝟙 (⊤_ C)) (by simp [U, V]) (by simp [U, V])
  have hq : (trivialFibrations C).functorCategory WalkingSpan q := by
    rintro (_ | _ | _)
    · exact (trivialFibrations C).id_mem X
    · exact hp
    · exact (trivialFibrations C).id_mem _
  have := hi q hq
  let bot : D ⟶ V := spanHomMk a b (terminal.from _) sq.w.symm (terminal.hom_ext _ _)
  have sq' : CommSq (hP.to U) i q bot := ⟨hP.hom_ext _ _⟩
  refine CommSq.HasLift.mk' {
    l := sq'.lift.app WalkingSpan.left
    fac_left := ?_
    fac_right := congr_app sq'.fac_right WalkingSpan.left }
  have hn := sq'.lift.naturality WalkingSpan.Hom.fst
  have hc := congr_app sq'.fac_right WalkingSpan.zero
  change sq'.lift.app WalkingSpan.zero ≫ 𝟙 X = a at hc
  change D.map WalkingSpan.Hom.fst ≫ sq'.lift.app WalkingSpan.left =
    sq'.lift.app WalkingSpan.zero ≫ 𝟙 X at hn
  exact hn.trans hc

include hP hi in
lemma snd_cofibration : cofibrations C (D.map WalkingSpan.Hom.snd) := by
  rw [← trivialFibrations_llp C]
  intro X Y p hp
  constructor
  intro a b sq
  let U := span (terminal.from X) (𝟙 X)
  let V := span (terminal.from X) p
  let q : U ⟶ V := spanHomMk (𝟙 X) (𝟙 (⊤_ C)) p (by simp [U, V]) (by simp [U, V])
  have hq : (trivialFibrations C).functorCategory WalkingSpan q := by
    rintro (_ | _ | _)
    · exact (trivialFibrations C).id_mem X
    · exact (trivialFibrations C).id_mem _
    · exact hp
  have := hi q hq
  let bot : D ⟶ V := spanHomMk a (terminal.from _) b (terminal.hom_ext _ _) sq.w.symm
  have sq' : CommSq (hP.to U) i q bot := ⟨hP.hom_ext _ _⟩
  refine CommSq.HasLift.mk' {
    l := sq'.lift.app WalkingSpan.right
    fac_left := ?_
    fac_right := congr_app sq'.fac_right WalkingSpan.right }
  have hn := sq'.lift.naturality WalkingSpan.Hom.snd
  have hc := congr_app sq'.fac_right WalkingSpan.zero
  change sq'.lift.app WalkingSpan.zero ≫ 𝟙 X = a at hc
  change D.map WalkingSpan.Hom.snd ≫ sq'.lift.app WalkingSpan.right =
    sq'.lift.app WalkingSpan.zero ≫ 𝟙 X at hn
  exact hn.trans hc

end SerrePositivity.DiagramModel.SpanCofibrations

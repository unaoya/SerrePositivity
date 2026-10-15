module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftSuccessor
public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftLimit

/-! # Actual coherent diagram lifts by well-order induction

Successor lifts use only the indicated lifting property at the new stage.
Limit lifts use the proved continuity of the source diagram. The target
and the map to be lifted need not be continuous.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.ContinuousLifts
variable {J : Type w} [LinearOrder J] [SuccOrder J] {C : Type u} [Category.{v} C]
  {D U V : J ⥤ C} (p : U ⟶ V) (b : D ⟶ V)
  (hstep : ∀ (j : J), ¬IsMax j →
    HasLiftingProperty (D.map (homOfLE (Order.le_succ j))) (p.app (Order.succ j)))

lemma successorSquare {j : J} (x : Partial p b j) :
    CommSq (x.hom j le_rfl ≫ U.map (homOfLE (Order.le_succ j)))
      (D.map (homOfLE (Order.le_succ j))) (p.app (Order.succ j)) (b.app (Order.succ j)) where
  w := by rw [Category.assoc, p.naturality, ← Category.assoc, x.fac, b.naturality]

def successor {j : J} (hj : ¬IsMax j) (x : Partial p b j) : Partial p b (Order.succ j) := by
  have := hstep j hj
  exact Partial.extendSucc x hj (successorSquare p b x).lift
    (successorSquare p b x).fac_left (successorSquare p b x).fac_right

lemma restrict_successor {j : J} (hj : ¬IsMax j) (x : Partial p b j) :
    (successor p b hstep hj x).restrict (Order.le_succ j) = x := by
  unfold successor
  exact Partial.restrict_extendSucc _ _ _ _ _

variable [D.IsWellOrderContinuous]

def inductionData : (system p b).WellOrderInductionData where
  succ _j hj x := successor p b hstep hj x
  map_succ _j hj x := restrict_successor p b hstep hj x
  lift _j hj s := Limit.extend s hj
  map_lift _j hj s i hi := Limit.restrict_extend s hj i hi

variable [OrderBot J] [WellFoundedLT J]

include hstep in
lemma exists_lift_with_base (x₀ : Partial p b ⊥) :
    ∃ l : D ⟶ U, l ≫ p = b ∧ l.app ⊥ = x₀.hom ⊥ le_rfl := by
  obtain ⟨s, hs⟩ := (inductionData p b hstep).surjective x₀
  let l : D ⟶ U := {
    app j := (s.val (Opposite.op j)).hom j le_rfl
    naturality i j f := by
      have h := s.property f.op
      change (s.val (Opposite.op j)).restrict (leOfHom f) = s.val (Opposite.op i) at h
      have hh := congrArg (fun x => x.hom i le_rfl) h
      exact ((s.val (Opposite.op j)).naturality (leOfHom f) le_rfl).trans
        (congrArg (fun t => t ≫ U.map f) hh) }
  refine ⟨l, ?_, ?_⟩
  · apply NatTrans.ext
    funext j
    exact (s.val (Opposite.op j)).fac j le_rfl
  · change s.val (Opposite.op ⊥) = x₀ at hs
    exact congrArg (fun x => x.hom ⊥ le_rfl) hs

include hstep in
lemma exists_lift (x₀ : Partial p b ⊥) : ∃ l : D ⟶ U, l ≫ p = b := by
  obtain ⟨l, hl, _⟩ := exists_lift_with_base p b hstep x₀
  exact ⟨l, hl⟩

end SerrePositivity.DiagramModel.ContinuousLifts

module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteFamily
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-! # Fiberwise all-monomorphism lifting assembles over arbitrary discrete labels

The prescribed label can vary across the parameter. The resulting lift
retains that entire label map and every already specified simplex.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.DiscreteFamily
variable {I : Type v} (F : I → SSet.{v})
  (hF : ∀ i, (MorphismProperty.monomorphisms SSet.{v}).rlp (terminal.from (F i)))

include hF in
lemma exists_extension {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
    (a : U ⟶ total F) (b : V ⟶ PiZeroConstant.discrete I)
    (hw : a ≫ projection F = j ≫ b) :
    ∃ l : V ⟶ total F, j ≫ l = a ∧ l ≫ projection F = b := by
  have hl : ∀ i, ∃ l : DiscreteFiber.obj b i ⟶ F i,
      DiscreteFiber.map j b i ≫ l = extract F (j ≫ b) a hw i := by
    intro i
    have : HasLiftingProperty (DiscreteFiber.map j b i) (terminal.from (F i)) :=
      hF i _ inferInstance
    let sq : CommSq (extract F (j ≫ b) a hw i) (DiscreteFiber.map j b i)
        (terminal.from (F i)) (terminal.from (DiscreteFiber.obj b i)) := ⟨by simp⟩
    exact ⟨sq.lift, sq.fac_left⟩
  let d := fun i => (hl i).choose
  refine ⟨assemble F b d, ?_, assemble_projection F b d⟩
  ext n x
  let i := b.app n (j.app n x)
  have hf := types_congr_hom (congr_app (hl i).choose_spec n)
    (⟨x, rfl⟩ : (DiscreteFiber.obj (j ≫ b) i).obj n)
  change assembleFn F b d n (j.app n x) = a.app n x
  calc
    _ = (⟨i, (d i).app n ⟨j.app n x, rfl⟩⟩ : (total F).obj n) := rfl
    _ = (⟨i, (extract F (j ≫ b) a hw i).app n ⟨x, rfl⟩⟩ : (total F).obj n) :=
      congrArg (Sigma.mk i) hf
    _ = _ := extractFn_spec F (j ≫ b) a hw i n ⟨x, rfl⟩

include hF in
lemma projection_mono_rlp :
    (MorphismProperty.monomorphisms SSet.{v}).rlp (projection F) := by
  intro U V j hj
  have : Mono j := hj
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨l, hl, hp⟩ := exists_extension F hF j a b sq.w
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := hp }⟩⟩

include hF in
lemma projection_localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (projection F)) :=
  MonoRightLiftingContraction.localized_isIso _ (projection_mono_rlp F hF)

end SerrePositivity.SimplicialModel.DiscreteFamily

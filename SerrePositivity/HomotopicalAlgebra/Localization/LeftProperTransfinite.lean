module

public import SerrePositivity.HomotopicalAlgebra.Localization.ContinuousLocalEquivalences
public import SerrePositivity.HomotopicalAlgebra.Localization.LeftProperPushout

/-! # Full transfinite closure of original cofibrant local equivalences

Both closure classes used by Smith recognition are proved for the original
W_S. Arbitrary well-orders in the presentability universe are allowed,
including limit stages of small cofinality and noncofibrant initial objects.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]


include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma cof_localEquivalences_transfiniteStableOfShape (S : MorphismProperty C)
    (K : Type w) [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S) K := by
  rw [MorphismProperty.isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨d⟩
  have : d.F.IsWellOrderContinuous := d.isWellOrderContinuous
  have hlocal := localEquivalence_transfinite_cocone cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S d.F d.map_mem (Cocone.mk Y d.incl) d.isColimit
  have hcof : cofibrations C (d.incl.app ⊥) := by
    apply (trivialFibrations_llp C).le
    intro A B p hp
    exact HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := d.isColimit) (fun k hk => MorphismProperty.hasLiftingProperty_of_wfs
        (d.F.map (homOfLE (Order.le_succ k))) p (d.map_mem k hk).1 hp)
  have hcofIso := (cofibrations C).of_isIso d.isoBot.inv
  have hlocalIso := weakEquivalences_le_localEquivalences cof fib hcofV S d.isoBot.inv
    ((weakEquivalences C).of_isIso d.isoBot.inv)
  exact ⟨d.fac ▸ (cofibrations C).comp_mem _ _ hcofIso hcof,
    d.fac ▸ (localEquivalences.{v, u} (C := C) cof fib S).comp_mem _ _ hlocalIso hlocal⟩

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma cof_localEquivalences_transfiniteStable (S : MorphismProperty C) :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S) where
  isStableUnderTransfiniteCompositionOfShape K _ _ _ _ :=
    cof_localEquivalences_transfiniteStableOfShape cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S K

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
/-- The two original closure conditions required by Smith recognition. -/
lemma localEquivalences_leftProperClosure (S : MorphismProperty C) :
    (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChange ∧
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S) :=
  ⟨cof_localEquivalences_pushoutStable cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S,
    cof_localEquivalences_transfiniteStable cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S⟩

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
/-- The same proved closure conditions in Smith's original generated-class notation. -/
lemma localEquivalences_smithClosure (S : MorphismProperty C) :
    (I.rlp.llp ⊓ localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChange ∧
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (I.rlp.llp ⊓ localEquivalences.{v, u} (C := C) cof fib S) := by
  have he : I.rlp.llp ⊓ localEquivalences.{v, u} (C := C) cof fib S =
      cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S :=
    congrArg (fun P => P ⊓ localEquivalences.{v, u} (C := C) cof fib S)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J).symm
  exact he.symm ▸ localEquivalences_leftProperClosure cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S

end SerrePositivity.Bousfield

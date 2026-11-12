module

public import SerrePositivity.HomotopicalAlgebra.Localization.SpanLocalEquivalences
public import SerrePositivity.HomotopicalAlgebra.Diagram.RelativeHomotopyColimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.LimitPrefix

/-! # Local equivalences along continuous transfinite cofibration sequences

Every limit stage is handled by its actual hocolim comparison, without
any restriction on cofinality or on cofibrancy of the initial object.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

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


variable {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localEquivalence_colimit_inclusion_of_pointwise (S : MorphismProperty C)
    (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hstep : ∀ k, ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k))))
    (hpoint : ∀ k, localEquivalences.{v, u} (C := C) cof fib S (D.map (homOfLE bot_le : ⊥ ⟶ k)))
    (c : Cocone D) (hc : IsColimit c) :
    localEquivalences.{v, u} (C := C) cof fib S (c.ι.app ⊥) := by
  have hcolim := HocolimSourceTests.localEquivalence_colim_of_weakComparisons
    K I J IS JS cof fib hcof hfib hw hcofV hfibV hcofB hfibB S (ContinuousLifts.fromBottom D)
    hpoint (HomotopyColimit.comparison_weakEquivalence_const I J (D.obj ⊥))
    (HomotopyColimit.comparison_weakEquivalence_of_continuous_leftProper I J D hstep)
  apply localEquivalence_of_colimit_comparison cof fib hcofV K S (ContinuousLifts.fromBottom D)
    (ColimitFromBottom.constCocone K (D.obj ⊥)) (ColimitFromBottom.constIsColimit K (D.obj ⊥))
    c hc (c.ι.app ⊥) _ hcolim
  intro k
  change 𝟙 (D.obj ⊥) ≫ c.ι.app ⊥ = D.map (homOfLE bot_le : ⊥ ⟶ k) ≫ c.ι.app k
  exact (Category.id_comp _).trans (c.w (homOfLE bot_le)).symm

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localEquivalence_from_bottom (S : MorphismProperty C)
    (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hstep : ∀ k, ¬IsMax k → (cofibrations C ⊓
      localEquivalences.{v, u} (C := C) cof fib S) (D.map (homOfLE (Order.le_succ k)))) :
    ∀ k, localEquivalences.{v, u} (C := C) cof fib S (D.map (homOfLE bot_le : ⊥ ⟶ k)) := by
  intro k
  induction k using SuccOrder.limitRecOn with
  | isMin k hk =>
    obtain rfl : k = ⊥ := by simpa using hk
    simpa only [homOfLE_refl, D.map_id] using
      (localEquivalences.{v, u} (C := C) cof fib S).id_mem (D.obj ⊥)
  | succ k hk ih =>
    have h := (localEquivalences.{v, u} (C := C) cof fib S).comp_mem _ _ ih (hstep k hk).2
    have he : D.map (homOfLE bot_le : ⊥ ⟶ k) ≫ D.map (homOfLE (Order.le_succ k)) =
        D.map (homOfLE bot_le : ⊥ ⟶ Order.succ k) := (D.map_comp _ _).symm
    exact he ▸ h
  | isSuccLimit k hk ih =>
    let := LimitPrefix.orderBot k hk
    let := LimitPrefix.succOrder k hk
    let E := (Set.principalSegIio k).monotone.functor ⋙ D
    have : E.IsWellOrderContinuous :=
      inferInstanceAs
        ((Set.principalSegIio k : Set.Iio k ≤i K).monotone.functor ⋙ D).IsWellOrderContinuous
    have hs (i : Set.Iio k) (_hi : ¬IsMax i) :
        cofibrations C (E.map (homOfLE (Order.le_succ i))) := by
      change cofibrations C (D.map (homOfLE (Order.le_succ i.val)))
      exact (hstep i.val (not_isMax_iff.mpr ⟨k, i.property⟩)).1
    have hp (i : Set.Iio k) : localEquivalences.{v, u} (C := C) cof fib S
        (E.map (homOfLE bot_le : ⊥ ⟶ i)) := ih i.val i.property
    exact localEquivalence_colimit_inclusion_of_pointwise cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S E hs hp ((Set.principalSegIio k).cocone D)
      (D.isColimitOfIsWellOrderContinuous k hk)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localEquivalence_transfinite_cocone (S : MorphismProperty C)
    (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hstep : ∀ k, ¬IsMax k → (cofibrations C ⊓
      localEquivalences.{v, u} (C := C) cof fib S) (D.map (homOfLE (Order.le_succ k))))
    (c : Cocone D) (hc : IsColimit c) :
    localEquivalences.{v, u} (C := C) cof fib S (c.ι.app ⊥) :=
  localEquivalence_colimit_inclusion_of_pointwise cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S D (fun k hk => (hstep k hk).1)
    (localEquivalence_from_bottom cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S D hstep) c hc

end SerrePositivity.Bousfield

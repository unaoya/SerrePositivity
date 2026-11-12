module

public import SerrePositivity.HomotopicalAlgebra.Localization.SpanLocalEquivalences
public import Mathlib.CategoryTheory.Category.ULift

/-! # Pushout closure of original cofibrant local equivalences

The original model's left properness supplies actual homotopy-pushout
comparisons. The RMap formula then proves that pushing out an original
cofibration in W_S along any map remains in W_S. No localized model
structure or cofibrancy of the objects is assumed.
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

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localEquivalence_of_pushout (S : MorphismProperty C)
    {A B D P : C} {f : A ⟶ B} {g : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    (s : IsPushout f g l r) (hf : cofibrations C f)
    (hflocal : localEquivalences.{v, u} (C := C) cof fib S f) :
    localEquivalences.{v, u} (C := C) cof fib S r := by
  let K := AsSmall.{w} WalkingSpan
  let e : K ≌ WalkingSpan := AsSmall.equiv.symm
  let a₀ : span (𝟙 A) g ⟶ span f g :=
    spanHomMk (𝟙 A) f (𝟙 D) (by simp) (by simp)
  let a := Functor.whiskerLeft e.functor a₀
  have hD : cofibrations C
      ((e.functor ⋙ span (𝟙 A) g).map (e.inverse.map WalkingSpan.Hom.fst)) := by
    change cofibrations C (𝟙 A)
    exact (cofibrations C).id_mem A
  have hE : cofibrations C
      ((e.functor ⋙ span f g).map (e.inverse.map WalkingSpan.Hom.fst)) := hf
  have ha : ∀ k, localEquivalences.{v, u} (C := C) cof fib S (a.app k) := by
    intro k
    change localEquivalences.{v, u} (C := C) cof fib S (a₀.app (e.functor.obj k))
    generalize e.functor.obj k = j
    rcases j with (_ | _ | _)
    · exact weakEquivalences_le_localEquivalences cof fib hcofV S _
        ((weakEquivalences C).id_mem A)
    · exact hflocal
    · exact weakEquivalences_le_localEquivalences cof fib hcofV S _
        ((weakEquivalences C).id_mem D)
  have hcolim := localEquivalence_span_colim cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB K e S a hD hE ha
  have s₀ : IsPushout (𝟙 A) g g (𝟙 D) := IsPushout.of_horiz_isIso ⟨by simp⟩
  apply localEquivalence_of_colimit_comparison cof fib hcofV K S a
    (s₀.cocone.whisker e.functor) (s₀.isColimit.whiskerEquivalence e)
    (s.cocone.whisker e.functor) (s.isColimit.whiskerEquivalence e) r _ hcolim
  intro k
  change s₀.cocone.ι.app (e.functor.obj k) ≫ r =
    a₀.app (e.functor.obj k) ≫ s.cocone.ι.app (e.functor.obj k)
  generalize e.functor.obj k = j
  rcases j with (_ | _ | _)
  · change (𝟙 A ≫ g) ≫ r = 𝟙 A ≫ (f ≫ l)
    simpa only [Category.id_comp] using s.w.symm
  · change g ≫ r = f ≫ l
    exact s.w.symm
  · change 𝟙 D ≫ r = 𝟙 D ≫ r
    rfl

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
/-- The pushout-stability input for Smith recognition, for the original W_S. -/
lemma cof_localEquivalences_pushoutStable (S : MorphismProperty C) :
    (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChange where
  of_isPushout s hf :=
    ⟨(cofibrations C).of_isPushout s hf.1,
      localEquivalence_of_pushout cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
        S s.flip hf.1 hf.2⟩

end SerrePositivity.Bousfield

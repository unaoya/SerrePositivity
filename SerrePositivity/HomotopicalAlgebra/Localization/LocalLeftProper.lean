module

public import SerrePositivity.HomotopicalAlgebra.Localization.SpanLocalEquivalences
public import Mathlib.CategoryTheory.Category.ULift

/-! # Left properness for the actual local-equivalence class

Pushout along an original cofibration preserves every local equivalence.
This is proved from homotopy-pushout comparisons in the original model,
before introducing the localized model structure.
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
lemma localEquivalence_of_pushout_along_cofibration (S : MorphismProperty C)
    {A B D P : C} {f : A ⟶ B} {g : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    (s : IsPushout f g l r) (hf : cofibrations C f)
    (hg : localEquivalences.{v, u} (C := C) cof fib S g) :
    localEquivalences.{v, u} (C := C) cof fib S l := by
  let K := AsSmall.{w} WalkingSpan
  let e : K ≌ WalkingSpan := AsSmall.equiv.symm
  let a₀ : span f (𝟙 A) ⟶ span f g :=
    spanHomMk (𝟙 A) (𝟙 B) g (by simp) (by simp)
  let a := Functor.whiskerLeft e.functor a₀
  have hD : cofibrations C
      ((e.functor ⋙ span f (𝟙 A)).map (e.inverse.map WalkingSpan.Hom.fst)) := hf
  have hE : cofibrations C
      ((e.functor ⋙ span f g).map (e.inverse.map WalkingSpan.Hom.fst)) := hf
  have ha : ∀ k, localEquivalences.{v, u} (C := C) cof fib S (a.app k) := by
    intro k
    change localEquivalences.{v, u} (C := C) cof fib S (a₀.app (e.functor.obj k))
    generalize e.functor.obj k = j
    rcases j with (_ | _ | _)
    · exact weakEquivalences_le_localEquivalences cof fib hcofV S _
        ((weakEquivalences C).id_mem A)
    · exact weakEquivalences_le_localEquivalences cof fib hcofV S _
        ((weakEquivalences C).id_mem B)
    · exact hg
  have hcolim := localEquivalence_span_colim cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB K e S a hD hE ha
  have s₀ : IsPushout f (𝟙 A) (𝟙 B) f := IsPushout.of_vert_isIso ⟨by simp⟩
  apply localEquivalence_of_colimit_comparison cof fib hcofV K S a
    (s₀.cocone.whisker e.functor) (s₀.isColimit.whiskerEquivalence e)
    (s.cocone.whisker e.functor) (s.isColimit.whiskerEquivalence e) l _ hcolim
  intro k
  change s₀.cocone.ι.app (e.functor.obj k) ≫ l =
    a₀.app (e.functor.obj k) ≫ s.cocone.ι.app (e.functor.obj k)
  generalize e.functor.obj k = j
  rcases j with (_ | _ | _)
  · change (f ≫ 𝟙 B) ≫ l = 𝟙 A ≫ (f ≫ l)
    simp only [Category.comp_id, Category.id_comp]
  · change 𝟙 B ≫ l = 𝟙 B ≫ l
    rfl
  · change f ≫ l = g ≫ r
    exact s.w

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localEquivalences_leftProper (S : MorphismProperty C) :
    (localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChangeAgainst
      (cofibrations C) where
  isStableUnderCobaseChangeAlong {_X _Y} _f hf := ⟨fun s hg =>
    localEquivalence_of_pushout_along_cofibration cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S s hf hg⟩

end SerrePositivity.Bousfield

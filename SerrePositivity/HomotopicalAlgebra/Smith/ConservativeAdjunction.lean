module

public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Presentable.Adjunction

/-! # Local presentability transported along a conservative forgetful adjunction

An accessible, faithful, conservative right adjoint transports a small strong
generator to free objects. Cocompleteness of the target is a separate input;
no local presentability or monadicity of that target is assumed.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.ConservativeAdjunction
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [G.Faithful] [G.ReflectsIsomorphisms]

include adj in
lemma strongGenerator_strictMap {P : ObjectProperty C} (hP : P.IsStrongGenerator) :
    (P.strictMap F).IsStrongGenerator := by
  have := adj.isRightAdjoint
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨?_, ?_⟩
  · intro X Y f g h
    apply G.map_injective
    apply hP.isSeparating
    intro A hA a
    have he := h (F.obj A) ⟨A, hA⟩ ((adj.homEquiv A X).symm a)
    have he' := congrArg (adj.homEquiv A Y) he
    rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right,
      Equiv.apply_symm_apply] at he'
    exact he'
  · intro X Y i _ hi
    have : IsIso (G.map i) := hP.isIso_of_mono (G.map i) (by
      intro A hA a
      obtain ⟨b, hb⟩ := hi (F.obj A) ⟨A, hA⟩ ((adj.homEquiv A Y).symm a)
      refine ⟨adj.homEquiv A X b, ?_⟩
      have hb' := congrArg (adj.homEquiv A Y) hb
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] at hb'
      exact hb')
    exact isIso_of_reflects_iso i G

include adj in
lemma isCardinalLocallyPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ] [G.IsCardinalAccessible κ]
    [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D] :
    IsCardinalLocallyPresentable D κ := by
  obtain ⟨P, _, hP, hp⟩ :=
    (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator C κ).mp inferInstance
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator D κ).mpr
  refine ⟨P.strictMap F, inferInstance, strongGenerator_strictMap adj hP, ?_⟩
  rintro _ ⟨X, hX⟩
  have := hp X hX
  exact adj.isCardinalPresentable_leftAdjoint_obj κ X

include adj in
lemma isLocallyPresentable [IsLocallyPresentable.{w} C] [G.IsAccessible.{w}]
    [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D] :
    IsLocallyPresentable.{w} D := by
  obtain ⟨κC, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  obtain ⟨κG, _, _⟩ := Functor.IsAccessible.exists_cardinal (F := G)
  let κ := κC ⊔ κG
  have : Fact κ.IsRegular := ⟨iteInduction (fun _ ↦ Fact.out) (fun _ ↦ Fact.out)⟩
  have := IsCardinalLocallyPresentable.of_le (C := C) (show κC ≤ κ from le_sup_left)
  have := Functor.isCardinalAccessible_of_le G (show κG ≤ κ from le_sup_right)
  exact ⟨κ, inferInstance, isCardinalLocallyPresentable adj κ⟩

end SerrePositivity.Smith.ConservativeAdjunction

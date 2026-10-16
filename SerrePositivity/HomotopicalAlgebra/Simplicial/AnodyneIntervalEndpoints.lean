module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceSpace
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-! # Interval endpoints are anodyne without any full model structure -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.AnodyneHomotopy

lemma delta_anodyne (i j : Fin 2) (hij : i ≠ j) :
    SSet.anodyneExtensions.{v} (SSet.stdSimplex.δ i) := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro E B p hp
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  refine ⟨fun {a b} sq => ?_⟩
  let fs : ∀ (k : Fin 2) (_ : k ≠ j),
      SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ E := fun _ _ => a
  have hc : SSet.horn.IsCompatible fs := True.intro
  have comm : ∀ (k : Fin 2) (hk : k ≠ j), fs k hk ≫ p = SSet.stdSimplex.δ k ≫ b := by
    intro k hk
    have he : k = i := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    subst k
    exact sq.w
  obtain ⟨l, hl, hr⟩ := hc.exists_lift p b comm
  exact ⟨⟨{ l := l, fac_left := hl i hij, fac_right := hr }⟩⟩

abbrev pointTensorIso (X : SSet.{v}) : X ≅ X ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 0) :=
  (ρ_ X).symm ≪≫ whiskerLeftIso X RelativeChoiceSpace.pointUnitIso.symm

lemma endpoint_zero_factor (X : SSet.{v}) :
    SSet.ι₀ = (pointTensorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (1 : Fin 2) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma endpoint_one_factor (X : SSet.{v}) :
    SSet.ι₁ = (pointTensorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (0 : Fin 2) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma endpoint_zero_anodyne (X : SSet.{v}) : SSet.anodyneExtensions (SSet.ι₀ (X := X)) := by
  rw [endpoint_zero_factor]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    ((delta_anodyne 1 0 (by decide)).whiskerLeft X)

lemma endpoint_one_anodyne (X : SSet.{v}) : SSet.anodyneExtensions (SSet.ι₁ (X := X)) := by
  rw [endpoint_one_factor]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    ((delta_anodyne 0 1 (by decide)).whiskerLeft X)

end SerrePositivity.SimplicialModel.AnodyneHomotopy

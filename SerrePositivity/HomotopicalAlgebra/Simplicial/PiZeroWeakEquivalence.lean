module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryOne
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-! # Actual connected components of simplicial weak equivalences

Boundary lifting first shows that a trivial fibration induces a bijection
on the actual SSet.π₀. Fibrant Brown factorization then proves this for weak
equivalences between fibrant simplicial sets. No geometric comparison or
extra weak-equivalence axiom is assumed.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial

namespace SerrePositivity.SimplicialModel

lemma piZero_eq_of_same_image {X Y : SSet.{v}} (p : X ⟶ Y)
    [HasLiftingProperty (SSet.boundary 1).ι p] {x₀ x₁ : X _⦋0⦌}
    (hx : p.app _ x₀ = p.app _ x₁) : SSet.π₀.mk x₀ = SSet.π₀.mk x₁ := by
  let v₀ : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ X := SSet.yonedaEquiv.symm x₀
  let v₁ : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ X := SSet.yonedaEquiv.symm x₁
  let b : (SSet.boundary 1).toSSet ⟶ X :=
    HomotopyFunctionComplex.BoundaryOne.isColimit.desc (BinaryCofan.mk v₀ v₁)
  have hb₀ : SSet.boundary.ι (1 : Fin 2) ≫ b = v₀ :=
    HomotopyFunctionComplex.BoundaryOne.isColimit.fac (BinaryCofan.mk v₀ v₁) ⟨WalkingPair.left⟩
  have hb₁ : SSet.boundary.ι (0 : Fin 2) ≫ b = v₁ :=
    HomotopyFunctionComplex.BoundaryOne.isColimit.fac (BinaryCofan.mk v₀ v₁) ⟨WalkingPair.right⟩
  let collapse := SSet.stdSimplex.isTerminalObj₀.from
    (SSet.stdSimplex.obj (SimplexCategory.mk 1))
  let c := collapse ≫ v₀ ≫ p
  have hc (i : Fin 2) : SSet.stdSimplex.δ i ≫ collapse = 𝟙 _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hv : v₀ ≫ p = v₁ ≫ p := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, v₀, v₁, Equiv.apply_symm_apply] using hx
  have sq : CommSq b (SSet.boundary 1).ι p c := by
    constructor
    apply HomotopyFunctionComplex.BoundaryOne.isColimit.hom_ext
    rintro ⟨j⟩
    cases j
    · change SSet.boundary.ι (1 : Fin 2) ≫ (b ≫ p) =
        SSet.boundary.ι (1 : Fin 2) ≫ ((SSet.boundary 1).ι ≫ c)
      simp only [← Category.assoc, hb₀, SSet.boundary.ι_ι, c,
        ← Category.assoc, hc, Category.id_comp]
    · change SSet.boundary.ι (0 : Fin 2) ≫ (b ≫ p) =
        SSet.boundary.ι (0 : Fin 2) ≫ ((SSet.boundary 1).ι ≫ c)
      simp only [← Category.assoc, hb₁, SSet.boundary.ι_ι, c,
        ← Category.assoc, hc, Category.id_comp]
      exact hv.symm
  have he₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ sq.lift = v₀ := by
    rw [← SSet.boundary.ι_ι (1 : Fin 2), Category.assoc, sq.fac_left, hb₀]
  have he₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ sq.lift = v₁ := by
    rw [← SSet.boundary.ι_ι (0 : Fin 2), Category.assoc, sq.fac_left, hb₁]
  apply SSet.π₀.sound
  exact SSet.Edge.ofTruncated
    { edge := SSet.yonedaEquiv sq.lift
      src_eq := by
        change X.δ (1 : Fin 2) (SSet.yonedaEquiv sq.lift) = x₀
        rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, he₀]
        exact SSet.yonedaEquiv.apply_symm_apply x₀
      tgt_eq := by
        change X.δ (0 : Fin 2) (SSet.yonedaEquiv sq.lift) = x₁
        rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, he₁]
        exact SSet.yonedaEquiv.apply_symm_apply x₁ }

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma piZero_bijective_of_trivialFibration {X Y : SSet.{v}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] : Function.Bijective (SSet.mapπ₀ p) := by
  have hp : trivialFibrations SSet.{v} p := ⟨mem_fibrations p, mem_weakEquivalences p⟩
  have hc : cofibrations SSet.{v} (initial.to Y) := by
    rw [hcof]
    exact inferInstanceAs (Mono (initial.to Y))
  have : HasLiftingProperty (initial.to Y) p :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ hc hp
  have hb : cofibrations SSet.{v} (SSet.boundary 1).ι := by
    rw [hcof]
    exact inferInstanceAs (Mono _)
  have : HasLiftingProperty (SSet.boundary 1).ι p :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ hb hp
  have sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) := ⟨by simp⟩
  let s := sq.lift
  have hs : s ≫ p = 𝟙 Y := sq.fac_right
  have hleft (z : SSet.π₀ X) : SSet.mapπ₀ s (SSet.mapπ₀ p z) = z := by
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
    simp only [SSet.mapπ₀_mk]
    apply piZero_eq_of_same_image p
    exact types_congr_hom (congr_app hs (Opposite.op (SimplexCategory.mk 0))) (p.app _ x)
  have hright (z : SSet.π₀ Y) : SSet.mapπ₀ p (SSet.mapπ₀ s z) = z := by
    rw [← SSet.mapπ₀_comp_apply, hs, SSet.mapπ₀_id_apply]
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

include hcof in
lemma piZero_bijective_of_weakEquivalence_of_fibrant {X Y : SSet.{v}}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    Function.Bijective (SSet.mapπ₀ f) := by
  let F := SSet.π₀Functor.{v}
  let h := Classical.choice (inferInstance : Nonempty (FibrantBrownFactorization f))
  have : IsIso (F.map h.p) := (CategoryTheory.isIso_iff_bijective _).mpr
    (piZero_bijective_of_trivialFibration hcof h.p)
  have : IsIso (F.map h.r) := (CategoryTheory.isIso_iff_bijective _).mpr
    (piZero_bijective_of_trivialFibration hcof h.r)
  have hr : F.map h.i ≫ F.map h.r = 𝟙 _ := by rw [← F.map_comp, h.i_r, F.map_id]
  have : IsIso (F.map h.i) := (isIso_comp_right_iff _ (F.map h.r)).mp
    (hr.symm ▸ inferInstanceAs (IsIso (𝟙 _)))
  have : IsIso (F.map f) := by rw [← h.fac, F.map_comp]; infer_instance
  exact (CategoryTheory.isIso_iff_bijective (F.map f)).mp inferInstance

end SerrePositivity.SimplicialModel

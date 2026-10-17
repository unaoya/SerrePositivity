module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomHomotopyComparison
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseTelescope
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # compactな始域から見た導来Homの余積比較

余積自体をcompactと仮定しない。compact性は始域Pとそのtensor像にのみ要求する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismDerivedHom_additive : (endomorphismDerivedHom A D E hE).Additive := by
  rw [Localization.functor_additive_iff (moduleHomotopyToDerivedClosed A D)
    (moduleHomotopyQuasiIso A D)]
  exact Functor.additive_of_iso (endomorphismDerivedHomHomotopyIso A D E hE)

local instance : (endomorphismDerivedHom A D E hE).Additive :=
  endomorphismDerivedHom_additive A D E hE

include hE in
lemma endomorphismDerivedTensor_additive : (endomorphismDerivedTensor A D E).Additive :=
  (endomorphismDerivedAdjunction A D E hE).left_adjoint_additive

variable {J : Type u} (F : J → DerivedModuleCategory A D)

lemma endomorphismDerivedHom_sigmaComparison_projection (i : J) :
    sigmaComparison (endomorphismDerivedHom A D E hE) F ≫
        (endomorphismDerivedHom A D E hE).map (moduleDerivedCoproductProjection A D F i) =
      moduleDerivedCoproductProjection A (EndomorphismObject E)
        (fun j => (endomorphismDerivedHom A D E hE).obj (F j)) i := by
  apply Sigma.hom_ext
  intro j
  rw [ι_comp_sigmaComparison_assoc, ← CategoryTheory.Functor.map_comp]
  by_cases hji : j = i
  · subst j
    rw [moduleDerivedCoproductProjection_self, CategoryTheory.Functor.map_id,
      moduleDerivedCoproductProjection_self]
  · rw [moduleDerivedCoproductProjection_ne A D F j i hji, Functor.map_zero,
      moduleDerivedCoproductProjection_ne A (EndomorphismObject E) _ j i hji]

lemma endomorphismDerivedHom_sigmaHom_injective
    (P : DerivedModuleCategory A (EndomorphismObject E))
    (hP : moduleCompact A (EndomorphismObject E) P) :
    Function.Injective (fun f : P ⟶ ∐ fun j => (endomorphismDerivedHom A D E hE).obj (F j) =>
      f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F) := by
  intro f g hfg
  change f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F =
    g ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F at hfg
  apply sub_eq_zero.mp
  apply moduleCompact_hom_ext_zero A (EndomorphismObject E) hP _ (f - g)
  intro i
  rw [← endomorphismDerivedHom_sigmaComparison_projection A D E hE F i,
    sub_comp, ← Category.assoc, ← Category.assoc, hfg, sub_self]

lemma endomorphismDerivedHom_sigmaHom_surjective
    (P : DerivedModuleCategory A (EndomorphismObject E))
    (hLP : moduleCompact A D ((endomorphismDerivedTensor A D E).obj P)) :
    Function.Surjective (fun f : P ⟶ ∐ fun j => (endomorphismDerivedHom A D E hE).obj (F j) =>
      f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F) := by
  classical
  let := endomorphismDerivedTensor_additive A D E hE
  let adj := endomorphismDerivedAdjunction A D E hE
  intro f
  obtain ⟨t, g, hg⟩ := hLP J F ((adj.homEquiv P (∐ F)).symm f)
  refine ⟨∑ j ∈ t, adj.homEquiv P (F j) (g j) ≫
    Sigma.ι (fun j => (endomorphismDerivedHom A D E hE).obj (F j)) j, ?_⟩
  dsimp only
  rw [sum_comp]
  have he := congrArg (adj.homAddEquiv P (∐ F)) hg
  have hx : (adj.homAddEquiv P (∐ F)) ((adj.homEquiv P (∐ F)).symm f) = f :=
    (adj.homEquiv P (∐ F)).apply_symm_apply f
  rw [hx] at he
  simp only [map_sum] at he
  calc
    _ = ∑ j ∈ t, adj.homEquiv P (∐ F) (g j ≫ Sigma.ι F j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Category.assoc, ι_comp_sigmaComparison]
      exact (adj.homEquiv_naturality_right (g j) (Sigma.ι F j)).symm
    _ = f := he

lemma endomorphismDerivedHom_sigmaHom_bijective
    (P : DerivedModuleCategory A (EndomorphismObject E))
    (hP : moduleCompact A (EndomorphismObject E) P)
    (hLP : moduleCompact A D ((endomorphismDerivedTensor A D E).obj P)) :
    Function.Bijective (fun f : P ⟶ ∐ fun j => (endomorphismDerivedHom A D E hE).obj (F j) =>
      f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F) :=
  ⟨endomorphismDerivedHom_sigmaHom_injective A D E hE F P hP,
    endomorphismDerivedHom_sigmaHom_surjective A D E hE F P hLP⟩

end SerrePositivity.DifferentialGraded

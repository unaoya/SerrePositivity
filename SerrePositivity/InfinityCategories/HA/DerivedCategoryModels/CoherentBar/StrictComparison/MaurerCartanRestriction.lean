module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanDescent
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated

/-!
概要：分裂包含で保たれる部分加群に Maurer–Cartan 方程式を制限する。
方針：包含後の cochain の単射性で判定し、微分と合成の保存を使う。
規約：追加微分の閉性と二乗零を別々に仮定しない。
使われ方：単体次元を切った実 bar 加群の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R]

lemma dgBarCochainMaurerCartan_restrict {L K : Complex R} (i : L ⟶ K) (r : K ⟶ L)
    (hir : i ≫ r = 𝟙 L) (ψ : Cochain L L 1) (θ : Cochain K K 1)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1))
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) :
    δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  apply cochain_postcomp_injective_of_retraction i r hir L 2
  dsimp only
  rw [Cochain.add_comp, Cochain.zero_comp, ← δ_comp_ofHom, ← hi, δ_ofHom_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← hi,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, ← hi,
    Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_add, hθ,
    Cochain.comp_zero]

section Module
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarModuleMaurerCartan_restrict {M N : ModuleCategory R D}
    (i : N ⟶ M) (r : M ⟶ N) (hir : i ≫ r = 𝟙 N)
    (ψ : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N)).X 1)
    (θ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M)).X 1)
    (hi : (eHomWhiskerRight (Complex R) i M).f 1 θ =
      (eHomWhiskerLeft (Complex R) N i).f 1 ψ)
    (hθ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M)).d 1 2 θ +
      compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) M)
        θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N)).d 1 2 ψ +
      compose R (x := ForgetEnrichment.to (Complex R) N)
        (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) N)
        ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  apply moduleHomElement_ext R D
  intro x
  rw [map_add, map_zero, moduleHomElement_d_π, moduleHomCompose_π]
  have hi' := congrArg (fun z => ((moduleHomπ R D
    (ForgetEnrichment.to (Complex R) N) (ForgetEnrichment.to (Complex R) M) x).f 1 z)) hi
  rw [moduleHomWhiskerRight_apply_π, moduleHomWhiskerLeft_apply_π] at hi'
  apply dgBarCochainMaurerCartan_restrict
    ((moduleEvaluation R D x).map i) ((moduleEvaluation R D x).map r) ?_ _ _ hi'
    (moduleMaurerCartan_evaluation R D (ForgetEnrichment.to (Complex R) M) θ hθ x)
  rw [← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]

end Module
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

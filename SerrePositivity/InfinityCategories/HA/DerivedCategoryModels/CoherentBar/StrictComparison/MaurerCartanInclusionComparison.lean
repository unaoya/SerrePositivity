module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanModuleMap

/-!
概要：二つの MC 部分加群の包含と可換する内部射は、制限 θ とも可換する。
方針：共通標的への分裂包含の後合成で判定する。
規約：全 dg Hom の等式を各評価の全 cochain 成分で判定する。
使われ方：単体次元の段階を増やす実 dg 加群射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R]

lemma dgBarCochain_comparison_of_inclusions {L M K : Complex R}
    (i : L ⟶ K) (j : M ⟶ K) (r : K ⟶ M) (hj : j ≫ r = 𝟙 M)
    (f : L ⟶ M) (hf : f ≫ j = i)
    (θ : Cochain K K 1) (ψ : Cochain L L 1) (χ : Cochain M M 1)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1))
    (hχ : (Cochain.ofHom j).comp θ (zero_add 1) = χ.comp (Cochain.ofHom j) (add_zero 1)) :
    (Cochain.ofHom f).comp χ (zero_add 1) = ψ.comp (Cochain.ofHom f) (add_zero 1) := by
  apply cochain_postcomp_injective_of_retraction j r hj L 1
  dsimp only
  rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← hχ,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hf, hi,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, hf]

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarModuleTheta_comparison_of_inclusions {L M K : ModuleCategory R D}
    (i : L ⟶ K) (j : M ⟶ K) (r : K ⟶ M) (hj : j ≫ r = 𝟙 M)
    (f : L ⟶ M) (hf : f ≫ j = i)
    (θ : (moduleHom R D (ForgetEnrichment.to (Complex R) K)
      (ForgetEnrichment.to (Complex R) K)).X 1)
    (ψ : (moduleHom R D (ForgetEnrichment.to (Complex R) L)
      (ForgetEnrichment.to (Complex R) L)).X 1)
    (χ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M)).X 1)
    (hi : (eHomWhiskerRight (Complex R) i K).f 1 θ =
      (eHomWhiskerLeft (Complex R) L i).f 1 ψ)
    (hχ : (eHomWhiskerRight (Complex R) j K).f 1 θ =
      (eHomWhiskerLeft (Complex R) M j).f 1 χ) :
    (eHomWhiskerRight (Complex R) f M).f 1 χ =
      (eHomWhiskerLeft (Complex R) L f).f 1 ψ := by
  apply moduleHomElement_ext R D
  intro x
  have hi' := congrArg (fun z => (moduleHomπ R D
    (ForgetEnrichment.to (Complex R) L) (ForgetEnrichment.to (Complex R) K) x).f 1 z) hi
  have hχ' := congrArg (fun z => (moduleHomπ R D
    (ForgetEnrichment.to (Complex R) M) (ForgetEnrichment.to (Complex R) K) x).f 1 z) hχ
  erw [moduleHomWhiskerRight_apply_π, moduleHomWhiskerLeft_apply_π] at hi' hχ' ⊢
  apply dgBarCochain_comparison_of_inclusions
    ((moduleEvaluation R D x).map i) ((moduleEvaluation R D x).map j)
    ((moduleEvaluation R D x).map r) ?_ ((moduleEvaluation R D x).map f) ?_ _ _ _ hi' hχ'
  · rw [← CategoryTheory.Functor.map_comp, hj, CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, hf]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

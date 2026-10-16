module
public import SerrePositivity.DifferentialGraded.Bimodule.RestrictedRepresentableAction
public import SerrePositivity.DifferentialGraded.Module.Free
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation

/-! # 積dg圏の代表加群の右制限と自由加群との全Hom自然な同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def restrictedRepresentableIso (b₀ : B) (c₀ c : C) :
    (tensorRightRestriction A B C c).obj
        (ForgetEnrichment.of (Complex A)
          (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) ≅
      (freeAt b₀).obj (c₀ ⟶[Complex A] c) :=
  moduleIsoMk A B
    (M := restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c)
      (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))))
    (N := freeModule b₀ (c₀ ⟶[Complex A] c))
    (fun x => signedSwap (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)) (by
      intro x y
      apply hom_naturality_of_apply
      intro p f
      apply Cochain.ext
      intro k n hn
      rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
        Cochain.ofHom_v, Cochain.ofHom_v]
      apply mapBifunctor.hom_ext
      intro r s hk
      change r + s = k at hk
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro h g
      change (signedSwap (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).hom.f n
        (moduleAction A
          (restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
            (tensorRightRestrictionInclusion A B C c)
            (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) f
          (ιTensorObj (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) r s k hk (h ⊗ₜ[A] g)) hn) =
        moduleAction A (freeModule b₀ (c₀ ⟶[Complex A] c)) f
          ((signedSwap (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).hom.f k
            (ιTensorObj (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) r s k hk (h ⊗ₜ[A] g))) hn
      rw [restrictedRepresentable_action, signedSwap_apply, signedSwap_apply]
      rw [moduleAction_units_smul]
      rw [tensorModule_action (c₀ ⟶[Complex A] c) (representable A b₀) x y p s r k
        (r + p) n (by omega) rfl hn, representable_action]
      simp only [smul_smul, ← Int.negOnePow_add]
      rw [show (r + p) * s = r * s + p * s by ring])

@[simp]
lemma restrictedRepresentableIso_hom_eval (b₀ : B) (c₀ c : C) (b : B) :
    (moduleEvaluation A B b).map (restrictedRepresentableIso A B C b₀ c₀ c).hom =
      (signedSwap (b ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).hom :=
  moduleIsoMk_hom_eval A B _ _ b

@[simp]
lemma restrictedRepresentableIso_inv_eval (b₀ : B) (c₀ c : C) (b : B) :
    (moduleEvaluation A B b).map (restrictedRepresentableIso A B C b₀ c₀ c).inv =
      (signedSwap (b ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)).inv :=
  moduleIsoMk_inv_eval A B _ _ b

end SerrePositivity.DifferentialGraded

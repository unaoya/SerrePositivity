module
public import SerrePositivity.DifferentialGraded.Bimodule.ClosedTransforms

/-! # 閉零bimodule変換の右加群射成分と全Hom自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory BraidedCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma closedFamily_naturality_converse {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ (c c' : C), (β_ (𝟙_ (Complex A)) (c ⟶[Complex A] c')).hom ≫
      (M.toFunctor.map c c' ⊗ₘ ForgetEnrichment.homTo (Complex A) (a c')) ≫
        eComp (Complex A) (M.rightAt c) (M.rightAt c') (N.rightAt c') =
      (ForgetEnrichment.homTo (Complex A) (a c) ⊗ₘ N.toFunctor.map c c') ≫
        eComp (Complex A) (M.rightAt c) (N.rightAt c) (N.rightAt c')) (c c' : C) :
    M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
    N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c) := by
  have hh := congrArg (fun k => (λ_ (c ⟶[Complex A] c')).inv ≫ k) (h c c')
  rw [braiding_tensorUnit_left] at hh
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hh
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc] at hh
  exact hh

/-- 単位パラメータの全豊穣変換を右B加群射として評価する。 -/
def closedTransApp {M N : Bimodule A B C}
    (τ : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N) (c : C) :
    ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c) :=
  ForgetEnrichment.homOf (Complex A) (τ.app c)

lemma closedTransApp_naturality {M N : Bimodule A B C}
    (τ : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N) (c c' : C) :
    M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c')
        (closedTransApp A B C τ c') =
    N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c')
        (closedTransApp A B C τ c) := by
  apply closedFamily_naturality_converse A B C (closedTransApp A B C τ)
  intro x y
  have ht := τ.naturality x y
  change (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
    (M.toFunctor.map x y ⊗ₘ τ.app y) ≫
      eComp (Complex A) (M.rightAt x) (M.rightAt y) (N.rightAt y) =
    (τ.app x ⊗ₘ N.toFunctor.map x y) ≫
      eComp (Complex A) (M.rightAt x) (N.rightAt x) (N.rightAt y) at ht
  simpa only [closedTransApp, ForgetEnrichment.homTo_homOf] using ht

@[simp]
lemma closedTransApp_closedFamilyTrans {M N : Bimodule A B C} (a) (h) (c : C) :
    closedTransApp A B C (closedFamilyTrans A B C (M := M) (N := N) a h) c = a c := rfl

lemma closedFamilyTrans_closedTransApp {M N : Bimodule A B C}
    (τ : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N) :
    closedFamilyTrans A B C (closedTransApp A B C τ)
      (closedTransApp_naturality A B C τ) = τ := by
  apply GradedNatTrans.ext
  funext c
  exact ForgetEnrichment.homTo_homOf (Complex A) (τ.app c)

end SerrePositivity.DifferentialGraded.Bimodule

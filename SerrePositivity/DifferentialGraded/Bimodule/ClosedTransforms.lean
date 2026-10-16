module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.HomWhisker

/-! # 全Hom自然なbimoduleの閉零豊穣自然変換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory BraidedCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左C作用も全Homに関して自然な、パラメータ付きbimodule変換。 -/
abbrev BimoduleParamTrans (K : Complex A) (M N : Bimodule A B C) :=
  GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M.toFunctor N.toFunctor

namespace Bimodule

/-- 右B加群射族の全Hom可換式から、左C作用に関する豊穣自然性を得る。 -/
lemma closedFamily_naturality {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c)) (c c' : C) :
    (β_ (𝟙_ (Complex A)) (c ⟶[Complex A] c')).hom ≫
      (M.toFunctor.map c c' ⊗ₘ ForgetEnrichment.homTo (Complex A) (a c')) ≫
        eComp (Complex A) (M.rightAt c) (M.rightAt c') (N.rightAt c') =
    (ForgetEnrichment.homTo (Complex A) (a c) ⊗ₘ N.toFunctor.map c c') ≫
      eComp (Complex A) (M.rightAt c) (N.rightAt c) (N.rightAt c') := by
  apply (cancel_epi (λ_ (c ⟶[Complex A] c')).inv).1
  rw [braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  exact h c c'

/-- 全次数自然な右加群射族を、単位パラメータのbimodule豊穣自然変換に束ねる。 -/
def closedFamilyTrans {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c)) :
    BimoduleParamTrans A B C (𝟙_ (Complex A)) M N where
  app c := ForgetEnrichment.homTo (Complex A) (a c)
  naturality := closedFamily_naturality A B C a h

@[simp]
lemma closedFamilyTrans_app {M N : Bimodule A B C} (a) (h) (c : C) :
    (closedFamilyTrans A B C (M := M) (N := N) a h).app c =
      ForgetEnrichment.homTo (Complex A) (a c) := rfl

end Bimodule
end SerrePositivity.DifferentialGraded

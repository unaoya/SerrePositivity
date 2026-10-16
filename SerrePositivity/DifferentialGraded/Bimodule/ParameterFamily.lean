module
public import SerrePositivity.DifferentialGraded.Bimodule.ParameterEvaluation
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # 全Hom自然なパラメータ付き右加群変換族からのbimodule変換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左加群の斉次cochainの符号付き交換式から全Hom自然性を復元する。 -/
lemma leftParamNaturality_of_cochain {C : Type w} [DGCategory A C]
    {K : Complex A} {M N : LeftModule A C}
    (a : ∀ c, K ⟶ homComplex A (M.obj c) (N.obj c))
    (h : ∀ (c c' : C) (k p m : ℤ) (hm : k + p = m)
      (t : K.X k) (f : GradedHom A c c' p),
      ((M.map c c').f p f).comp ((a c').f k t) (by omega) =
        (k * p).negOnePow • (((a c).f k t).comp ((N.map c c').f p f) hm)) (c c' : C) :
    (β_ K (c ⟶[Complex A] c')).hom ≫
      (M.map c c' ⊗ₘ a c') ≫ enrichedComposition _ _ _ =
    (a c ⊗ₘ N.map c c') ≫ enrichedComposition _ _ _ := by
  have hh := moduleParamNaturality_of_cochain A
    (M := M.toRightOpposite) (N := N.toRightOpposite) (fun x => a x.unop.unop)
    (fun x y k p m hm t f => by
      change (((𝟙 _ ≫ M.map x.unop.unop y.unop.unop).f p f).comp
          ((a y.unop.unop).f k t) (by omega)) =
        (k * p).negOnePow • (((a x.unop.unop).f k t).comp
          ((𝟙 _ ≫ N.map x.unop.unop y.unop.unop).f p f) hm)
      simpa only [Category.id_comp] using h x.unop.unop y.unop.unop k p m hm t f)
    (op (op c)) (op (op c'))
  change (β_ K (c ⟶[Complex A] c')).hom ≫
      ((𝟙 _ ≫ M.map c c') ⊗ₘ a c') ≫ enrichedComposition _ _ _ =
    (a c ⊗ₘ (𝟙 _ ≫ N.map c c')) ≫ enrichedComposition _ _ _ at hh
  simpa only [Category.id_comp] using hh

variable (B : Type v) (C : Type w) [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左右の全Hom自然性を保持する変換族を主bimodule変換へ束ねる。 -/
def paramFamilyTrans {K : Complex A} {M N : Bimodule A B C}
    (a : ∀ c, ModuleParamTrans A B K (M.rightAt c) (N.rightAt c))
    (h : ∀ (b : B) (c c' : C), (β_ K (c ⟶[Complex A] c')).hom ≫
      ((M.leftAt b).map c c' ⊗ₘ (a c').app (op b)) ≫ enrichedComposition _ _ _ =
      ((a c).app (op b) ⊗ₘ (N.leftAt b).map c c') ≫ enrichedComposition _ _ _) :
    BimoduleParamTrans A B C K M N where
  app c := (moduleHomEquiv A B K (M.rightAt c) (N.rightAt c)).symm (a c)
  naturality c c' := by
    apply moduleHom_ext
    intro b
    change (β_ K (c ⟶[Complex A] c')).hom ≫
        (M.toFunctor.map c c' ⊗ₘ (moduleHomEquiv A B K _ _).symm (a c')) ≫
          moduleComposition A B (M.rightAt c) (M.rightAt c') (N.rightAt c') ≫
            moduleHomπ A B (M.rightAt c) (N.rightAt c') b =
      ((moduleHomEquiv A B K _ _).symm (a c) ⊗ₘ N.toFunctor.map c c') ≫
        moduleComposition A B (M.rightAt c) (N.rightAt c) (N.rightAt c') ≫
          moduleHomπ A B (M.rightAt c) (N.rightAt c') b
    rw [moduleComposition_π, moduleComposition_π]
    simp only [tensorHom_comp_tensorHom_assoc, moduleHomEquiv_symm_π]
    exact h b c c'

@[simp]
lemma paramFamilyTrans_value {K : Complex A} {M N : Bimodule A B C} (a h) (b : B) (c : C) :
    paramValue A B C (paramFamilyTrans A B C (K := K) (M := M) (N := N) a h) b c =
      (a c).app (op b) := moduleHomEquiv_symm_π A B K _ _ (a c) b

end SerrePositivity.DifferentialGraded.Bimodule

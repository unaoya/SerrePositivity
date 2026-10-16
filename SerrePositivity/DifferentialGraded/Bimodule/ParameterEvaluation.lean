module
public import SerrePositivity.DifferentialGraded.Bimodule.ClosedTransforms
public import SerrePositivity.DifferentialGraded.Module.LeftCategory

/-! # 任意パラメータのbimodule変換の両対象評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
variable {K : Complex A} {M N : Bimodule A B C}

/-- パラメータ付き変換を両対象で評価するchain map。 -/
def paramValue (τ : BimoduleParamTrans A B C K M N) (b : B) (c : C) :
    K ⟶ homComplex A (M.value b c) (N.value b c) :=
  τ.app c ≫ moduleHomπ A B (M.rightAt c) (N.rightAt c) b

/-- 左対象を固定すると全次数自然な右B加群変換になる。 -/
def paramRightAt (τ : BimoduleParamTrans A B C K M N) (c : C) :
    ModuleParamTrans A B K (M.rightAt c) (N.rightAt c) :=
  moduleHomEquiv A B K (M.rightAt c) (N.rightAt c) (τ.app c)

@[simp]
lemma paramRightAt_app (τ : BimoduleParamTrans A B C K M N) (b : B) (c : C) :
    (paramRightAt A B C τ c).app (op b) = paramValue A B C τ b c := rfl

lemma paramValue_right_naturality (τ : BimoduleParamTrans A B C K M N)
    (c : C) (b b' : Bᵒᵖ) :
    (β_ K (b ⟶[Complex A] b')).hom ≫
      ((M.rightAt c).map b b' ⊗ₘ paramValue A B C τ b'.unop c) ≫
        enrichedComposition _ _ _ =
    (paramValue A B C τ b.unop c ⊗ₘ (N.rightAt c).map b b') ≫
      enrichedComposition _ _ _ :=
  (paramRightAt A B C τ c).naturality b b'

/-- Hom endの合成を評価すると、左C作用に関する全Hom自然性が得られる。 -/
lemma paramValue_left_naturality (τ : BimoduleParamTrans A B C K M N)
    (b : B) (c c' : C) :
    (β_ K (c ⟶[Complex A] c')).hom ≫
      ((M.leftAt b).map c c' ⊗ₘ paramValue A B C τ b c') ≫ enrichedComposition _ _ _ =
    (paramValue A B C τ b c ⊗ₘ (N.leftAt b).map c c') ≫ enrichedComposition _ _ _ := by
  have h := congrArg (fun f => f ≫
    moduleHomπ A B (M.rightAt c) (N.rightAt c') b) (τ.naturality c c')
  change (β_ K (c ⟶[Complex A] c')).hom ≫
      (M.toFunctor.map c c' ⊗ₘ τ.app c') ≫
        moduleComposition A B (M.rightAt c) (M.rightAt c') (N.rightAt c') ≫
          moduleHomπ A B (M.rightAt c) (N.rightAt c') b =
    (τ.app c ⊗ₘ N.toFunctor.map c c') ≫
      moduleComposition A B (M.rightAt c) (N.rightAt c) (N.rightAt c') ≫
        moduleHomπ A B (M.rightAt c) (N.rightAt c') b at h
  rw [moduleComposition_π, moduleComposition_π] at h
  simp only [tensorHom_comp_tensorHom_assoc] at h
  exact h

/-- 右対象を固定した全次数自然な左C加群変換。Cのsmall性は不要。 -/
def paramLeftAt (τ : BimoduleParamTrans A B C K M N) (b : B) :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj K)
      (M.leftAt b) (N.leftAt b) where
  app c := paramValue A B C τ b c
  naturality := paramValue_left_naturality A B C τ b

@[simp]
lemma paramLeftAt_app (τ : BimoduleParamTrans A B C K M N) (b : B) (c : C) :
    (paramLeftAt A B C τ b).app c = paramValue A B C τ b c := rfl

/-- パラメータ付きbimodule変換の等式を全ての値で判定する。 -/
lemma paramValue_ext {τ υ : BimoduleParamTrans A B C K M N}
    (h : ∀ b c, paramValue A B C τ b c = paramValue A B C υ b c) : τ = υ := by
  apply GradedNatTrans.ext
  funext c
  apply moduleHom_ext
  intro b
  exact h b c

end SerrePositivity.DifferentialGraded.Bimodule

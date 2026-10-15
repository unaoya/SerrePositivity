module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # 全次数自然な左作用族からのbimodule構成子 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左作用の全次数自然性と各評価での単位・合成からbimoduleを構成する。 -/
def ofParamTrans (P : C → RightModule A B)
    (a : ∀ c c' : C, ModuleParamTrans A B (c ⟶[Complex A] c') (P c) (P c'))
    (hi : ∀ (c : C) (b : Bᵒᵖ),
      eId (Complex A) c ≫ (a c c).app b = identity ((P c).obj b))
    (hc : ∀ (c c' c'' : C) (b : Bᵒᵖ),
      eComp (Complex A) c c' c'' ≫ (a c c'').app b =
        ((a c c').app b ⊗ₘ (a c' c'').app b) ≫ enrichedComposition _ _ _) :
    Bimodule A B C where
  obj := P
  map c c' := (moduleHomEquiv A B _ _ _).symm (a c c')
  map_id c := by
    apply moduleHom_ext
    intro b
    rw [Category.assoc, moduleHomEquiv_symm_π]
    exact (hi c (op b)).trans (moduleIdentity_π A B (P c) b).symm
  map_comp c c' c'' := by
    apply moduleHom_ext
    intro b
    rw [Category.assoc, moduleHomEquiv_symm_π]
    change eComp (Complex A) c c' c'' ≫ (a c c'').app (op b) =
      (_ ⊗ₘ _) ≫ moduleComposition A B (P c) (P c') (P c'') ≫
        moduleHomπ A B (P c) (P c'') b
    rw [moduleComposition_π, tensorHom_comp_tensorHom_assoc,
      moduleHomEquiv_symm_π, moduleHomEquiv_symm_π]
    exact hc c c' c'' (op b)

/-- 構成子の左作用を取り出すと元の作用族になる。 -/
lemma ofParamTrans_map_π (P : C → RightModule A B) (a hi hc) (c c' : C) (b : B) :
    (ofParamTrans A B C P a hi hc).toFunctor.map c c' ≫
      moduleHomπ A B (P c) (P c') b = (a c c').app (op b) :=
  moduleHomEquiv_symm_π A B _ _ _ _ b

variable {A B C}

/-- bimoduleから全次数自然な左作用族を取り出す。 -/
def paramTrans (M : Bimodule A B C) (c c' : C) :
    ModuleParamTrans A B (c ⟶[Complex A] c') (M.rightAt c) (M.rightAt c') :=
  moduleHomEquiv A B _ _ _ (M.toFunctor.map c c')

lemma paramTrans_unit (M : Bimodule A B C) (c : C) (b : Bᵒᵖ) :
    eId (Complex A) c ≫ (M.paramTrans c c).app b = identity ((M.rightAt c).obj b) := by
  change eId (Complex A) c ≫ M.toFunctor.map c c ≫
    moduleHomπ A B (M.rightAt c) (M.rightAt c) b.unop = _
  rw [← Category.assoc, M.toFunctor.map_id]
  exact moduleIdentity_π A B (M.rightAt c) b.unop

lemma paramTrans_comp (M : Bimodule A B C) (c c' c'' : C) (b : Bᵒᵖ) :
    eComp (Complex A) c c' c'' ≫ (M.paramTrans c c'').app b =
      ((M.paramTrans c c').app b ⊗ₘ (M.paramTrans c' c'').app b) ≫
        enrichedComposition _ _ _ := by
  change eComp (Complex A) c c' c'' ≫ M.toFunctor.map c c'' ≫
    moduleHomπ A B (M.rightAt c) (M.rightAt c'') b.unop = _
  rw [← Category.assoc, M.toFunctor.map_comp]
  change (M.toFunctor.map c c' ⊗ₘ M.toFunctor.map c' c'') ≫
    moduleComposition A B (M.rightAt c) (M.rightAt c') (M.rightAt c'') ≫
      moduleHomπ A B (M.rightAt c) (M.rightAt c'') b.unop = _
  rw [moduleComposition_π, tensorHom_comp_tensorHom_assoc]
  rfl

/-- 抽出した作用族からbimoduleを再構成すると元に戻る。 -/
lemma ofParamTrans_recover (M : Bimodule A B C) :
    ofParamTrans A B C M.rightAt M.paramTrans M.paramTrans_unit M.paramTrans_comp = M := by
  change (ofParamTrans A B C M.rightAt M.paramTrans
    M.paramTrans_unit M.paramTrans_comp).toFunctor = M.toFunctor
  apply EnrichedFunctor.ext (Complex A)
    (F := (ofParamTrans A B C M.rightAt M.paramTrans
      M.paramTrans_unit M.paramTrans_comp).toFunctor) (G := M.toFunctor) (fun _ => rfl)
  intro c c'
  change (moduleHomEquiv A B _ _ _).symm
    ((moduleHomEquiv A B _ _ _) (M.toFunctor.map c c')) ≫ 𝟙 _ = M.toFunctor.map c c'
  simp

end SerrePositivity.DifferentialGraded.Bimodule

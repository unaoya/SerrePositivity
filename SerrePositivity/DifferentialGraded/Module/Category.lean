module
public import SerrePositivity.DifferentialGraded.Module.Composition

/-! # Hom end による右 dg 加群圏の豊穣構造 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- end 合成の左単位則は各対象の左単位則から従う。 -/
lemma moduleIdentity_comp (M N : RightModule A D) :
    (λ_ (moduleHom A D M N)).inv ≫ moduleIdentity A D M ▷ _ ≫
      moduleComposition A D M M N = 𝟙 _ := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, moduleComposition_π]
  change _ ≫ (moduleIdentity A D M ⊗ₘ 𝟙 _) ≫
    (moduleHomπ A D M M x ⊗ₘ moduleHomπ A D M N x) ≫ enrichedComposition _ _ _ = _
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [moduleIdentity_π, Category.id_comp]
  rw [tensorHom_def', Category.assoc]
  rw [← leftUnitor_inv_naturality_assoc, identity_comp]
  simp

/-- end 合成の右単位則は各対象の右単位則から従う。 -/
lemma moduleComp_identity (M N : RightModule A D) :
    (ρ_ (moduleHom A D M N)).inv ≫ _ ◁ moduleIdentity A D N ≫
      moduleComposition A D M N N = 𝟙 _ := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, moduleComposition_π]
  change _ ≫ (𝟙 _ ⊗ₘ moduleIdentity A D N) ≫
    (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N N x) ≫ enrichedComposition _ _ _ = _
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [moduleIdentity_π, Category.id_comp]
  rw [tensorHom_def, Category.assoc]
  rw [← rightUnitor_inv_naturality_assoc, comp_identity]
  simp

/-- end 合成の結合則は各対象の豊穣結合則から従う。 -/
lemma moduleComposition_assoc (M N P Q : RightModule A D) :
    (α_ (moduleHom A D M N) (moduleHom A D N P) (moduleHom A D P Q)).inv ≫
      moduleComposition A D M N P ▷ _ ≫ moduleComposition A D M P Q =
    _ ◁ moduleComposition A D N P Q ≫ moduleComposition A D M N Q := by
  apply moduleHom_ext
  intro x
  simp only [Category.assoc, moduleComposition_π]
  change (α_ _ _ _).inv ≫ (moduleComposition A D M N P ⊗ₘ 𝟙 _) ≫
      (moduleHomπ A D M P x ⊗ₘ moduleHomπ A D P Q x) ≫ enrichedComposition _ _ _ =
    (𝟙 _ ⊗ₘ moduleComposition A D N P Q) ≫
      (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N Q x) ≫ enrichedComposition _ _ _
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, moduleComposition_π]
  rw [← tensorHom_comp_whiskerRight_assoc
    (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N P x)
    (enrichedComposition _ _ _) (moduleHomπ A D P Q x)]
  rw [← tensorHom_comp_whiskerLeft_assoc (moduleHomπ A D M N x)
    (moduleHomπ A D N P x ⊗ₘ moduleHomπ A D P Q x) (enrichedComposition _ _ _)]
  rw [← associator_inv_naturality_assoc (moduleHomπ A D M N x)
    (moduleHomπ A D N P x) (moduleHomπ A D P Q x)]
  have he := enrichedComposition_assoc (M.obj (Opposite.op x)) (N.obj (Opposite.op x))
    (P.obj (Opposite.op x)) (Q.obj (Opposite.op x))
  have he' := congrArg (fun f => (α_ _ _ _).inv ≫ f) he
  simp only [Iso.inv_hom_id_assoc] at he'
  rw [he']

/-- 右 dg 加群圏の主モデル。Hom は全次数自然変換の end。 -/
instance moduleEnrichment : DGCategory A (RightModule A D) :=
  ofHomObjects A (RightModule A D) (moduleHom A D) (moduleIdentity A D)
    (moduleComposition A D) (moduleIdentity_comp A D) (moduleComp_identity A D)
    (moduleComposition_assoc A D)

/-- 閉次数零の右 dg 加群圏。通常の関手圏の射には置き換えない。 -/
abbrev ModuleCategory := ClosedCategory A (RightModule A D)
/-- 対象での評価は主 Hom end から Ch(A) への豊穣関手。 -/
def moduleEvaluationDG (x : D) : DGFunctor A (RightModule A D) (Complex A) where
  obj M := M.obj (Opposite.op x)
  map M N := moduleHomπ A D M N x
  map_id M := moduleIdentity_π A D M x
  map_comp M N P := moduleComposition_π A D M N P x

/-- 閉次数零加群圏での評価を既存 chain map 圏へ接続する。 -/
def moduleEvaluation (x : D) : ModuleCategory A D ⥤ Complex A :=
  (moduleEvaluationDG A D x).forget ⋙ closedToComplex A

/-- 閉次数零射は単位複体パラメータ付きの全次数自然変換。 -/
def moduleClosedHomEquiv (M N : ModuleCategory A D) :
    (M ⟶ N) ≃ ModuleParamTrans A D (𝟙_ (Complex A))
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) :=
  moduleHomEquiv A D _ _ _
end SerrePositivity.DifferentialGraded

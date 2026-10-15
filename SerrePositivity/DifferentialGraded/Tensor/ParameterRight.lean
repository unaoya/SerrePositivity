module
public import SerrePositivity.DifferentialGraded.Tensor.ParameterRightAction
public import SerrePositivity.DifferentialGraded.Tensor.Elements

/-! # 右加群変数のパラメータ付きbalanced tensor作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全次数自然な右加群射の族はbalanced族を誘導する。 -/
def rightParamFamily {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) :
    ParamFamily A D M N K (obj A D M' N) := by
  refine ⟨fun x => (α_ K (M.obj (op x)) (N.obj x)).inv ≫
    (uncurryRight (a (op x)) ▷ N.obj x) ≫ ι A D M' N x, ?_⟩
  intro x y
  have h := congrArg (fun t => (α_ K (M.obj (op y)) (x ⟶[Complex A] y)).inv ≫ t)
    (paramRightAction A D a ha x y)
  simp only [Iso.inv_hom_id_assoc] at h
  dsimp only
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, h,
    comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [condition, associator_naturality_left_assoc,
    pentagon_inv_inv_hom_hom_inv_assoc,
    ← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc,
    ← whiskerLeft_comp_assoc]

/-- K⊗(M⊗_D N)からM'⊗_D Nへの実際のchain map。 -/
def rightParamMap {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) :
    K ⊗ obj A D M N ⟶ obj A D M' N :=
  paramDesc A D M N (rightParamFamily A D N a ha)

@[reassoc (attr := simp)]
lemma ι_rightParamMap {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) (x : D) :
    (K ◁ ι A D M N x) ≫ rightParamMap A D N a ha =
      (α_ K (M.obj (op x)) (N.obj x)).inv ≫
        (uncurryRight (a (op x)) ▷ N.obj x) ≫ ι A D M' N x :=
  ι_paramDesc A D M N (rightParamFamily A D N a ha) x

lemma rightParamMap_element {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) (x : D)
    {k r s n : ℤ} (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (hn : k + (r + s) = n) :
    (rightParamMap A D N a ha).f n
      (ιTensorObj K (obj A D M N) k (r + s) n hn
        (t ⊗ₜ[A] element A D M N x m v rfl)) =
    element A D M' N x (((a (op x)).f k t).v r (k + r) (by omega) m) v (by omega) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v))))
    (ι_rightParamMap A D N a ha x)
  change (rightParamMap A D N a ha).f n
    ((K ◁ ι A D M N x).f n
      (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
        (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v)))) =
    (ι A D M' N x).f n
      ((uncurryRight (a (op x)) ▷ N.obj x).f n
        ((α_ K (M.obj (op x)) (N.obj x)).inv.f n
          (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
            (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl
              (m ⊗ₜ[A] v))))) at h
  rw [whiskerLeft_apply, associator_inv_apply, whiskerRight_apply, uncurryRight_apply] at h
  exact h

/-- 右加群の主Hom複体からbalanced tensorの主Hom複体への射。 -/
def rightHomMap (M M' : RightModule A D) (N : LeftModule A D) :
    moduleHom A D M M' ⟶ homComplex A (obj A D M N) (obj A D M' N) :=
  paramHomMap A D M N (rightParamFamily A D N
    (fun x => moduleHomπ A D M M' x.unop) (moduleHomπ_naturality A D M M'))

@[reassoc]
lemma rightHomMap_ι (M M' : RightModule A D) (N : LeftModule A D) (x : D) :
    rightHomMap A D M M' N ≫ homPrecompose (ι A D M N x) (obj A D M' N) =
    curryRight ((α_ (moduleHom A D M M') (M.obj (op x)) (N.obj x)).inv ≫
      (uncurryRight (moduleHomπ A D M M' x) ▷ N.obj x) ≫ ι A D M' N x) :=
  paramHomMap_ι A D M N (rightParamFamily A D N
    (fun x => moduleHomπ A D M M' x.unop) (moduleHomπ_naturality A D M M')) x

end SerrePositivity.DifferentialGraded.BalancedTensor

module
public import SerrePositivity.DifferentialGraded.Tensor.ParameterLeftAction
public import SerrePositivity.DifferentialGraded.Tensor.Elements
public import SerrePositivity.DifferentialGraded.Complexes.ParameterCross

/-! # 左加群変数のパラメータ付きbalanced tensor作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群の全次数自然なHom族を右加群値の後へ移してbalanced族にする。 -/
def leftParamFamily {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) :
    ParamFamily A D M N K (obj A D M N') := by
  refine ⟨fun x => parameterCross K (M.obj (op x)) (N.obj x) ≫
    (M.obj (op x) ◁ uncurryRight (a x)) ≫ ι A D M N' x, ?_⟩
  intro x y
  have h := congrArg (fun t => (α_ K (x ⟶[Complex A] y) (N.obj x)).inv ≫ t)
    (paramLeftAction A D a ha x y)
  simp only [Iso.inv_hom_id_assoc] at h
  have hc : (K ◁ leftAction A D N x y) ≫ uncurryRight (a y) =
      parameterCross K (x ⟶[Complex A] y) (N.obj x) ≫
        ((x ⟶[Complex A] y) ◁ uncurryRight (a x)) ≫ leftAction A D N' x y := by
    simpa only [parameterCross, Category.assoc] using h
  dsimp only
  rw [parameterCross_naturality_left_assoc, ← whisker_exchange_assoc,
    condition, associator_naturality_right_assoc, parameterCross_tensor_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [← hc, whiskerLeft_comp, Category.assoc, ← parameterCross_naturality_right_assoc,
    ← whiskerLeft_comp_assoc]

/-- K⊗(M⊗_D N)からM⊗_D N'への実際のchain map。 -/
def leftParamMap {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) :
    K ⊗ obj A D M N ⟶ obj A D M N' :=
  paramDesc A D M N (leftParamFamily A D M a ha)

@[reassoc (attr := simp)]
lemma ι_leftParamMap {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) (x : D) :
    (K ◁ ι A D M N x) ≫ leftParamMap A D M a ha =
      parameterCross K (M.obj (op x)) (N.obj x) ≫
        (M.obj (op x) ◁ uncurryRight (a x)) ≫ ι A D M N' x :=
  ι_paramDesc A D M N (leftParamFamily A D M a ha) x

/-- Kと右加群値の次数の積が左変数作用の符号になる。 -/
lemma leftParamMap_element {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) (x : D)
    {k r s n : ℤ} (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (hn : k + (r + s) = n) :
    (leftParamMap A D M a ha).f n
      (ιTensorObj K (obj A D M N) k (r + s) n hn
        (t ⊗ₜ[A] element A D M N x m v rfl)) =
    (k * r).negOnePow • element A D M N' x m
      (((a x).f k t).v s (k + s) (by omega) v) (by omega) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v))))
    (ι_leftParamMap A D M a ha x)
  change (leftParamMap A D M a ha).f n
    ((K ◁ ι A D M N x).f n
      (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
        (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v)))) =
    (ι A D M N' x).f n
      ((M.obj (op x) ◁ uncurryRight (a x)).f n
        ((parameterCross K (M.obj (op x)) (N.obj x)).f n
          (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
            (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl
              (m ⊗ₜ[A] v))))) at h
  rw [whiskerLeft_apply, parameterCross_apply] at h
  simp only [Units.smul_def, map_zsmul] at h
  rw [whiskerLeft_apply, uncurryRight_apply] at h
  simpa only [element, Units.smul_def] using h

/-- 左加群の主Hom複体からbalanced tensorの主Hom複体への射。 -/
def leftHomMap (M : RightModule A D) (N N' : LeftModule A D) :
    leftModuleHom A D N N' ⟶ homComplex A (obj A D M N) (obj A D M N') :=
  paramHomMap A D M N (leftParamFamily A D M
    (leftModuleHomπ A D N N') (leftModuleHomπ_naturality A D N N'))

@[reassoc]
lemma leftHomMap_ι (M : RightModule A D) (N N' : LeftModule A D) (x : D) :
    leftHomMap A D M N N' ≫ homPrecompose (ι A D M N x) (obj A D M N') =
    curryRight (parameterCross (leftModuleHom A D N N') (M.obj (op x)) (N.obj x) ≫
      (M.obj (op x) ◁ uncurryRight (leftModuleHomπ A D N N' x)) ≫ ι A D M N' x) :=
  paramHomMap_ι A D M N (leftParamFamily A D M
    (leftModuleHomπ A D N N') (leftModuleHomπ_naturality A D N N')) x

end SerrePositivity.DifferentialGraded.BalancedTensor

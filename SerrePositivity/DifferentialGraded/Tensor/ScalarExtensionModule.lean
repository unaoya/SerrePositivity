module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionHom
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Action
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange

/-! # dg 加群の対象の係数変更 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

@[reassoc]
lemma tensorIso_braiding (K L : Complex A) :
    (β_ ((extension φ).obj K) ((extension φ).obj L)).hom ≫ (tensorIso φ L K).inv =
      (tensorIso φ K L).inv ≫ (extension φ).map (β_ K L).hom := by
  apply (cancel_epi (tensorIso φ K L).hom).1
  rw [Iso.hom_inv_id_assoc]
  have h := congrArg (fun f => f ≫ (tensorIso φ L K).inv)
    (cochainTensorBaseChangeIso_symmetry φ K L)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  convert h.symm using 1

variable (D : Type v) [DGCategory A D]

/-- 係数変更と opposite を交換する恒等 Hom の dg 関手。
合成の符号は強モノイダル構造の braiding 整合性から得る。 -/
def oppositeDGFunctor :
    DGFunctor A' (DGBaseChange φ D)ᵒᵖ (DGBaseChange φ Dᵒᵖ) where
  obj x := op (show D from x.unop)
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp x y z := by
    change ((β_ _ _).hom ≫ (tensorIso φ _ _).inv ≫
      (extension φ).map (eComp (Complex A) (C := D) z.unop y.unop x.unop)) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (tensorIso φ _ _).inv ≫
          (extension φ).map ((β_ _ _).hom ≫
            eComp (Complex A) (C := D) z.unop y.unop x.unop)
    simp only [Category.comp_id, tensorHom_id, Functor.map_comp]
    rw [tensorIso_braiding_assoc]
    simp only [id_whiskerRight, Category.id_comp]

/-- 各値を係数拡大した右 dg 加群。作用は全次数 Hom 比較を通して定義する。 -/
def rightModule (M : RightModule A D) : RightModule A' (DGBaseChange φ D) :=
  ((oppositeDGFunctor φ D).comp (dgFunctor φ M.toFunctor)).comp (complexDGFunctor φ)

/-- 左 dg 加群の係数変更。 -/
def leftModule (M : LeftModule A D) : LeftModule A' (DGBaseChange φ D) :=
  (dgFunctor φ M).comp (complexDGFunctor φ)

lemma rightModule_obj (M : RightModule A D) (x : D) :
    (rightModule φ D M).obj (op x) = (extension φ).obj (M.obj (op x)) := rfl

lemma leftModule_obj (M : LeftModule A D) (x : D) :
    (leftModule φ D M).obj x = (extension φ).obj (M.obj x) := rfl

set_option backward.isDefEq.respectTransparency true in
lemma rightModule_action (M : RightModule A D) (x y : Dᵒᵖ) (p r n : ℤ)
    (h : r + p = n) (f : GradedHom A x y p) (m : (M.obj x).X r) :
    let := φ.toAlgebra
    moduleAction A' (rightModule φ D M) (x := x) (y := y)
      ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) h =
        (1 : A') ⊗ₜ[A] moduleAction A M f m h := by
  let := φ.toAlgebra
  change ((homComparison φ (M.obj x) (M.obj y)).f p
    ((ModuleCat.extendScalars φ).map ((M.map x y).f p)
      ((𝟙 ((extension φ).obj (x ⟶[Complex A] y)) :
        (extension φ).obj (x ⟶[Complex A] y) ⟶ (extension φ).obj (x ⟶[Complex A] y)).f p
          ((1 : A') ⊗ₜ[A] f)))).v r n h
        ((1 : A') ⊗ₜ[A] m) = _
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [ModuleCat.ExtendScalars.map_tmul φ,
    homComparison_apply φ (M.obj x) (M.obj y) p r n h]
  rfl

end SerrePositivity.DifferentialGraded.ScalarExtension

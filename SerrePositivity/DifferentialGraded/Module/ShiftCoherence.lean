module
public import SerrePositivity.DifferentialGraded.Module.Shift
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.Zero
public import SerrePositivity.DifferentialGraded.Complexes.ShiftCoherence
public import Mathlib.CategoryTheory.Shift.CommShift

/-! # 加群の零・加法 shift 比較と整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Mathlib の零 shift 比較の全次数自然な加群同型への持ち上げ。 -/
def moduleShiftZeroIsoObj (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (shiftModule 0 M) ≅ ForgetEnrichment.of (Complex A) M :=
  moduleIsoMk A D (M := shiftModule 0 M) (N := M)
    (fun x => (shiftFunctorZero (Complex A) ℤ).app (M.obj x)) (by
      intro x y
      change (M.map x y ≫ shiftHom 0 (M.obj x) (M.obj y)) ≫
        homPostcompose ((M.obj x)⟦(0 : ℤ)⟧)
          ((shiftFunctorZero (Complex A) ℤ).hom.app (M.obj y)) = _
      rw [Category.assoc, shiftHom_zero_naturality]
      rfl)

/-- Mathlib の加法 shift 比較の全次数自然な加群同型への持ち上げ。 -/
def moduleShiftAddIsoObj (s t : ℤ) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (shiftModule (s + t) M) ≅
      ForgetEnrichment.of (Complex A) (shiftModule t (shiftModule s M)) :=
  moduleIsoMk A D (M := shiftModule (s + t) M) (N := shiftModule t (shiftModule s M))
    (fun x => (shiftFunctorAdd (Complex A) s t).app (M.obj x)) (by
      intro x y
      change (M.map x y ≫ shiftHom (s + t) (M.obj x) (M.obj y)) ≫
        homPostcompose ((M.obj x)⟦s + t⟧)
          ((shiftFunctorAdd (Complex A) s t).hom.app (M.obj y)) =
        ((M.map x y ≫ shiftHom s (M.obj x) (M.obj y)) ≫
          shiftHom t ((M.obj x)⟦s⟧) ((M.obj y)⟦s⟧)) ≫
            homPrecompose ((shiftFunctorAdd (Complex A) s t).hom.app (M.obj x))
              (((M.obj y)⟦s⟧)⟦t⟧)
      simp only [Category.assoc]
      rw [shiftHom_add_naturality])

@[simp] lemma moduleShiftZeroIsoObj_hom_eval (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftZeroIsoObj A D M).hom =
      (shiftFunctorZero (Complex A) ℤ).hom.app (M.obj (op x)) :=
  moduleIsoMk_hom_eval A D _ _ x
@[simp] lemma moduleShiftZeroIsoObj_inv_eval (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftZeroIsoObj A D M).inv =
      (shiftFunctorZero (Complex A) ℤ).inv.app (M.obj (op x)) :=
  moduleIsoMk_inv_eval A D _ _ x
@[simp] lemma moduleShiftAddIsoObj_hom_eval (s t : ℤ) (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftAddIsoObj A D s t M).hom =
      (shiftFunctorAdd (Complex A) s t).hom.app (M.obj (op x)) :=
  moduleIsoMk_hom_eval A D _ _ x
@[simp] lemma moduleShiftAddIsoObj_inv_eval (s t : ℤ) (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftAddIsoObj A D s t M).inv =
      (shiftFunctorAdd (Complex A) s t).inv.app (M.obj (op x)) :=
  moduleIsoMk_inv_eval A D _ _ x

/-- 加群の零 shift 比較自然同型。 -/
def moduleShiftZeroIso : moduleShiftFunctor A D 0 ≅ 𝟭 (ModuleCategory A D) :=
  NatIso.ofComponents (fun M => moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M))
    (by
      intro M N f
      apply moduleMorphism_ext
      intro x
      simp only [moduleShiftFunctor, Functor.id_map,
        CategoryTheory.Functor.map_comp, moduleShiftMap_eval,
        moduleShiftZeroIsoObj_hom_eval]
      exact (shiftFunctorZero (Complex A) ℤ).hom.naturality ((moduleEvaluation A D x).map f))

/-- 加群の加法 shift 比較自然同型。 -/
def moduleShiftAddIso (s t : ℤ) :
    moduleShiftFunctor A D (s + t) ≅ moduleShiftFunctor A D s ⋙ moduleShiftFunctor A D t :=
  NatIso.ofComponents (fun M => moduleShiftAddIsoObj A D s t
    (ForgetEnrichment.to (Complex A) M)) (by
      intro M N f
      apply moduleMorphism_ext
      intro x
      simp only [moduleShiftFunctor, Functor.comp_map,
        CategoryTheory.Functor.map_comp, moduleShiftMap_eval,
        moduleShiftAddIsoObj_hom_eval]
      exact (shiftFunctorAdd (Complex A) s t).hom.naturality ((moduleEvaluation A D x).map f))

@[simp] lemma moduleShiftFunctor_map_eval (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftFunctor A D s).map f) =
      ((moduleEvaluation A D x).map f)⟦s⟧' := moduleShiftMap_eval A D s f x

@[simp] lemma moduleShiftZeroIso_hom_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftZeroIso A D).hom.app M) =
      (shiftFunctorZero (Complex A) ℤ).hom.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftZeroIsoObj_hom_eval A D _ x
@[simp] lemma moduleShiftZeroIso_inv_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftZeroIso A D).inv.app M) =
      (shiftFunctorZero (Complex A) ℤ).inv.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftZeroIsoObj_inv_eval A D _ x
@[simp] lemma moduleShiftAddIso_hom_eval (s t : ℤ) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftAddIso A D s t).hom.app M) =
      (shiftFunctorAdd (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftAddIsoObj_hom_eval A D s t _ x
@[simp] lemma moduleShiftAddIso_inv_eval (s t : ℤ) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftAddIso A D s t).inv.app M) =
      (shiftFunctorAdd (Complex A) s t).inv.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftAddIsoObj_inv_eval A D s t _ x

/-- 加群 shift の零・加法比較は複体 shift の整合性を満たす。 -/
def moduleShiftMkCore : ShiftMkCore (ModuleCategory A D) ℤ where
  F := moduleShiftFunctor A D
  zero := moduleShiftZeroIso A D
  add := moduleShiftAddIso A D
  assoc_hom_app s t r M := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleShiftFunctor_map_eval,
      moduleShiftAddIso_hom_eval, eqToHom_map]
    change (shiftFunctorAdd (Complex A) (s + t) r).hom.app
        ((moduleEvaluation A D x).obj M) ≫
      ((shiftFunctorAdd (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M))⟦r⟧' =
      eqToHom (congrArg (fun n : ℤ => ((moduleEvaluation A D x).obj M)⟦n⟧)
        (add_assoc s t r)) ≫
      (shiftFunctorAdd (Complex A) s (t + r)).hom.app ((moduleEvaluation A D x).obj M) ≫
      (shiftFunctorAdd (Complex A) t r).hom.app (((moduleEvaluation A D x).obj M)⟦s⟧)
    have h := shiftFunctorAdd_assoc_hom_app s t r ((moduleEvaluation A D x).obj M)
    simpa only [shiftFunctorAdd', Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc] using h
  zero_add_hom_app s M := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleShiftFunctor_map_eval,
      moduleShiftAddIso_hom_eval, moduleShiftZeroIso_inv_eval, eqToHom_map]
    exact shiftFunctorAdd_zero_add_hom_app s ((moduleEvaluation A D x).obj M)
  add_zero_hom_app s M := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleShiftAddIso_hom_eval,
      moduleShiftZeroIso_inv_eval, eqToHom_map]
    exact shiftFunctorAdd_add_zero_hom_app s ((moduleEvaluation A D x).obj M)

/-- 閉零 dg 加群圏の整数 shift。整合性は Mathlib の比較から証明した。 -/
instance moduleHasShift : HasShift (ModuleCategory A D) ℤ :=
  hasShiftMk _ _ (moduleShiftMkCore A D)

/-- 登録された shift は明示構成した関手と同じ。 -/
lemma moduleShiftFunctor_eq (s : ℤ) :
    CategoryTheory.shiftFunctor (ModuleCategory A D) s = moduleShiftFunctor A D s := rfl

lemma moduleShiftZero_eq :
    shiftFunctorZero (ModuleCategory A D) ℤ = moduleShiftZeroIso A D := rfl
lemma moduleShiftAdd_eq (s t : ℤ) :
    shiftFunctorAdd (ModuleCategory A D) s t = moduleShiftAddIso A D s t := rfl

/-- 加群の各整数 shift は加法的。 -/
instance moduleShiftFunctorAdditive (s : ℤ) : (moduleShiftFunctor A D s).Additive where
  map_add := by
    intro M N f g
    apply moduleMorphism_ext
    intro x
    simp only [moduleShiftFunctor_map_eval, Functor.map_add]

/-- 登録された整数 shift も加法的。 -/
instance moduleShiftAdditive (s : ℤ) :
    (CategoryTheory.shiftFunctor (ModuleCategory A D) s).Additive :=
  moduleShiftFunctorAdditive A D s

/-- 評価比較は零・加法 shift と整合する。 -/
instance moduleEvaluationCommShift (x : D) : (moduleEvaluation A D x).CommShift ℤ where
  commShiftIso := fun s => moduleShiftEvaluationIso A D s x
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [moduleShiftEvaluationIso, NatIso.ofComponents_hom_app,
      Functor.CommShift.isoZero_hom_app, moduleShiftZero_eq,
      moduleShiftZeroIso_hom_eval, Iso.hom_inv_id_app, Iso.refl_hom]
    rfl
  commShiftIso_add s t := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [Functor.CommShift.isoAdd_hom_app, moduleShiftAdd_eq,
      moduleShiftAddIso_hom_eval, moduleShiftEvaluationIso, NatIso.ofComponents_hom_app,
      Iso.refl_hom]
    change 𝟙 (((moduleEvaluation A D x).obj M)⟦s + t⟧) =
      (shiftFunctorAdd (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) ≫
      𝟙 ((((moduleEvaluation A D x).obj M)⟦s⟧)⟦t⟧) ≫
      (𝟙 (((moduleEvaluation A D x).obj M)⟦s⟧))⟦t⟧' ≫
      (shiftFunctorAdd (Complex A) s t).inv.app ((moduleEvaluation A D x).obj M)
    simp only [CategoryTheory.Functor.map_id]
    change 𝟙 _ = (shiftFunctorAdd (Complex A) s t).hom.app
        ((moduleEvaluation A D x).obj M) ≫
      𝟙 ((CategoryTheory.shiftFunctor (Complex A) s ⋙
        CategoryTheory.shiftFunctor (Complex A) t).obj ((moduleEvaluation A D x).obj M)) ≫
      (shiftFunctorAdd (Complex A) s t).inv.app ((moduleEvaluation A D x).obj M)
    rw [Category.id_comp]
    exact (Iso.hom_inv_id_app (shiftFunctorAdd (Complex A) s t) _).symm
end SerrePositivity.DifferentialGraded

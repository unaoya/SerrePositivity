module

public import SerrePositivity.AlgebraicGeometry.ProjectiveRightTensorLocalization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：標準開で用いる実際の加群の局所化と、余極限を比較する。
方針：分数の局所化関手を、局所化環とのテンソル積と自然同型で比較する。
規約：固定した共通の環で局所化する。零になる局所化も含む。
使われ方：動く基底の模型を共通係数へ制限した後の標準開の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open MonoidalCategory
universe u
variable {P : Type u} [CommRing P] (S : Submonoid P)

/-- 実際の局所化された加群を、元の係数環上の関手として扱う。 -/
def projectiveLocalizedModuleFunctor : ModuleCat.{u} P ⥤ ModuleCat.{u} P where
  obj M := ModuleCat.of P (LocalizedModule S M)
  map f := ModuleCat.ofHom (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
    (LocalizedModule.mkLinearMap S _) f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact IsLocalizedModule.map_id S (LocalizedModule.mkLinearMap S M)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using LocalizedModule.induction_on with
    | _ m s =>
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        IsLocalizedModule.map_LocalizedModules]

/-- 実際の分数の局所化は、局所化環とのテンソル積に自然に一致する。 -/
def projectiveLocalizedModuleTensorNatIso :
    projectiveLocalizedModuleFunctor S ≅
      tensorLeft (ModuleCat.of P (Localization S)) :=
  NatIso.ofComponents
    (fun M ↦ ((LocalizedModule.equivTensorProduct S M).restrictScalars P).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using LocalizedModule.induction_on with
      | _ m s =>
        change LocalizedModule.equivTensorProduct S N
            (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
              (LocalizedModule.mkLinearMap S N) f.hom (LocalizedModule.mk m s)) =
          ((tensorLeft (ModuleCat.of P (Localization S))).map f).hom
            (LocalizedModule.equivTensorProduct S M (LocalizedModule.mk m s))
        rw [IsLocalizedModule.map_LocalizedModules, LocalizedModule.equivTensorProduct_apply_mk,
          LocalizedModule.equivTensorProduct_apply_mk]
        rfl)

/-- 固定した環での実際の局所化は、任意の小さい余極限を保つ。 -/
instance projectiveLocalizedModuleFunctorPreservesColimits :
    PreservesColimitsOfSize.{u, u} (projectiveLocalizedModuleFunctor S) := by
  exact preservesColimits_of_natIso (projectiveLocalizedModuleTensorNatIso S).symm

/-- 実際の局所化と余極限の canonical な比較。 -/
def projectiveLocalizedColimitIso {J : Type u} [SmallCategory J]
    (M : J ⥤ ModuleCat.{u} P) :
    ModuleCat.of P (LocalizedModule S (colimit M : ModuleCat.{u} P)) ≅
      colimit (M ⋙ projectiveLocalizedModuleFunctor S) :=
  preservesColimitIso (projectiveLocalizedModuleFunctor S) M

/-- 局所化の余極限比較は、有限段からの分数の分子と分母を保つ。 -/
theorem projectiveLocalizedColimitIso_fraction {J : Type u} [SmallCategory J]
    (M : J ⥤ ModuleCat.{u} P) (j : J) (m : M.obj j) (s : S) :
    (projectiveLocalizedColimitIso S M).inv.hom
        ((colimit.ι (M ⋙ projectiveLocalizedModuleFunctor S) j).hom (LocalizedModule.mk m s)) =
      LocalizedModule.mk ((colimit.ι M j).hom m) s := by
  calc
    _ = IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (M.obj j))
        (LocalizedModule.mkLinearMap S (colimit M : ModuleCat.{u} P))
        (colimit.ι M j).hom (LocalizedModule.mk m s) :=
      congrArg (fun f ↦ f.hom (LocalizedModule.mk m s))
        (ι_preservesColimitIso_inv (projectiveLocalizedModuleFunctor S) M j)
    _ = _ := by rw [IsLocalizedModule.map_LocalizedModules]

/-- 実際の局所化と余極限の比較は、加群図式の射に自然。 -/
theorem projectiveLocalizedColimitIso_naturality {J : Type u} [SmallCategory J]
    {M N : J ⥤ ModuleCat.{u} P} (η : M ⟶ N) :
    (projectiveLocalizedModuleFunctor S).map (colim.map η) ≫
        (projectiveLocalizedColimitIso S N).hom =
      (projectiveLocalizedColimitIso S M).hom ≫
        colim.map (Functor.whiskerRight η (projectiveLocalizedModuleFunctor S)) :=
  (preservesColimitNatIso (projectiveLocalizedModuleFunctor S)).hom.naturality η

end SerrePositivity.AlgebraicGeometry

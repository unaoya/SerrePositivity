module
public import SerrePositivity.DifferentialGraded.StageTwo
public import Mathlib.Data.ZMod.Basic

/-! # U5 の非有界・非体・全次数の受入検証 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

-- 対象宇宙と Hom 宇宙は独立。end の smallness は明示する。
example [Small.{u} D] : DGCategory A (RightModule A D) := inferInstance
example [Small.{u} D] : Linear A (ModuleCategory A D) := inferInstance
example [Small.{u} D] (x : D) (M : RightModule A D) :
    moduleHom A D (representable A x) M ≅ M.obj (op x) := dgYonedaIso A x M
example [Small.{u} D] (x : D) : ModuleCategory A D ⥤ Complex A :=
  moduleEvaluation A D x

-- 同じ Yoneda は任意パラメータ複体で成り立ち、H⁰ に制限しない。
example (x : D) (M : RightModule A D) (K : Complex A) :
    ModuleParamTrans A D K (representable A x) M ≃ (K ⟶ M.obj (op x)) :=
  dgYonedaEquiv A x M K

-- 正負の次数の作用と変換が共存する成分で自然性を検証する。
example {K : Complex A} {M N : RightModule A D}
    (τ : ModuleParamTrans A D K M N) (x y : Dᵒᵖ) (r : ℤ)
    (t : K.X 1) (f : GradedHom A x y (-1)) (v : (M.obj x).X r) :
    ((τ.app y).f 1 t).v (r + (-1)) r (by omega) (moduleAction A M f v rfl) =
      (1 * (-1) : ℤ).negOnePow • moduleAction A N f
        (((τ.app x).f 1 t).v r (r + 1) rfl v) (by omega) :=
  moduleParamTrans_apply A τ (m := 0) t f v (by omega) (by omega)

-- 基本構成は体に限定しない。
example : ModuleCategory ℤ PUnit.{1} ≌ Complex ℤ := ringModuleEquivalence ℤ
example : ModuleCategory (ZMod 2) PUnit.{1} ≌ Complex (ZMod 2) :=
  ringModuleEquivalence (ZMod 2)
example (P Q : Complex (ZMod 2)) :
    moduleHom (ZMod 2) PUnit.{1} (ringModule (ZMod 2) P) (ringModule (ZMod 2) Q) ≅
      homComplex (ZMod 2) P Q := ringConstantHomIso (ZMod 2) P Q
example (M : RightModule ℤ PUnit.{1}) :
    ringModule ℤ (M.obj (op PUnit.unit)) = M := ringModule_recover ℤ M
end SerrePositivity.DifferentialGraded.Checks

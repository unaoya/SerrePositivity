module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Karoubi 包絡の線形構造

形式的直和因子の射に、元の圏のスカラー作用を制限する。
恒等射は元の対象の恒等射ではなく、その直和因子を切り出す冪等元である。
したがって、台の条件も冪等元のスカラー倍によって判定する。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents
open CategoryTheory.Functor

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]

instance karoubiHomModule (P Q : Karoubi C) : Module R (P ⟶ Q) where
  smul a f := ⟨a • f.f, by simp only [Linear.comp_smul, Linear.smul_comp, f.comm]⟩
  one_smul f := by ext; exact one_smul R f.f
  mul_smul a b f := by ext; exact mul_smul a b f.f
  smul_zero a := by ext; exact smul_zero a
  smul_add a f g := by ext; exact smul_add a f.f g.f
  add_smul a b f := by ext; exact add_smul a b f.f
  zero_smul f := by ext; exact zero_smul R f.f

instance karoubiLinear : Linear R (Karoubi C) where
  smul_comp _ _ _ a f g := by ext; apply Linear.smul_comp
  comp_smul _ _ _ f a g := by ext; apply Linear.comp_smul

/-- Karoubi 包絡のスカラー作用は元の射への作用そのものである。 -/
@[simp] lemma karoubi_smul_f {P Q : Karoubi C} (a : R) (f : P ⟶ Q) :
    (a • f).f = a • f.f := rfl

instance toKaroubi_linear : (toKaroubi C).Linear R where
  map_smul := by intros; rfl

variable {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  (F : C ⥤ D)

omit [Linear R C] [Linear R D] in
instance karoubiExtension_additive [F.Additive] :
    ((functorExtension₂ C D).obj F).Additive where
  map_add := by intros; ext; exact F.map_add

instance karoubiExtension_linear [F.Linear R] :
    ((functorExtension₂ C D).obj F).Linear R where
  map_smul := by intros; ext; exact F.map_smul _ _

omit [Linear R C] [Linear R D] in
/-- 冪等完備な値域への延長も加法的である。 -/
instance karoubiExtensionToComplete_additive [IsIdempotentComplete D] [F.Additive] :
    ((functorExtension C D).obj F).Additive := by
  change (((functorExtension₂ C D).obj F) ⋙ (toKaroubiEquivalence D).inverse).Additive
  infer_instance

omit [Preadditive C] [Linear R C] [Preadditive D] [Linear R D] in
/-- 冪等完備な値域への延長は、元の圏上では元の関手に自然同型である。 -/
noncomputable def karoubiExtensionToCompleteFactors [IsIdempotentComplete D] :
    toKaroubi C ⋙ (functorExtension C D).obj F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)
      (toKaroubiEquivalence D).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F (toKaroubiEquivalence D).unitIso.symm ≪≫ Functor.rightUnitor F

end SerrePositivity

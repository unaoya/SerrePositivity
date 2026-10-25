module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceQuotientSingle
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # 実根添加源の射影モデルの元の係数環への制限

源の二重多項式構造を使う。任意の環射について射影性を保存するとは主張しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => MvPolynomial (σ × ℕ) P₀
local notation "C₀" => algebraMap A L₀

/-- 二重多項式源上の射影加群は、二重係数包含に沿う実係数制限でも射影的。 -/
theorem deltaRootSourceCoefficientRestrict_projective (M : ModuleCat.{u} L₀) [Projective M] :
    Projective ((ModuleCat.restrictScalars C₀).obj M) := by
  let : Module.Free A L₀ := Module.Free.trans (R := A) (S := P₀) (M := L₀)
  have : Module.Projective L₀ M := inferInstance
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := L₀) (P := M)).mp inferInstance
  let F := ModuleCat.restrictScalars C₀
  let Y := ModuleCat.of L₀ (M →₀ L₀)
  let i : M ⟶ Y := ModuleCat.ofHom s
  let r : Y ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination L₀ id)
  have hir : i ≫ r = 𝟙 M := ModuleCat.hom_ext hs
  let e : F.obj Y ≃ₗ[A] (M →₀ L₀) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (M →₀ L₀) at x
        apply Finsupp.ext
        intro m
        change (algebraMap A L₀ r) * x m = r • x m
        rw [Algebra.smul_def] }
  have : Module.Projective A (F.obj Y) := Module.Projective.of_equiv e.symm
  have hM : Module.Projective A (F.obj M) :=
    Module.Projective.of_split (F.map i).hom (F.map r).hom (by
      apply ModuleCat.hom_ext_iff.mp
      change F.map i ≫ F.map r = 𝟙 (F.obj M)
      rw [← F.map_comp, hir, F.map_id])
  exact ModuleCat.projective_of_categoryTheory_projective (F.obj M)

/-- 指定した実源射影モデルを、実A係数制限対象の射影モデルへ変換する。 -/
def deltaRootSourceCoefficientModel
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    BoundedAboveDerivedModel (((boundedAboveDerivedRestrictScalars C₀).obj X).obj) where
  complex := ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex
  bound := P.bound
  bounded := inferInstance
  projective i := deltaRootSourceCoefficientRestrict_projective (P.complex.X i)
  iso := (boundedAboveDerivedRestrictScalarsModelIso C₀ X P).symm

/-- 元の係数環の任意イデアルでの実導来還元を、制限した具体的射影モデルで計算する。 -/
def deltaRootSourceCoefficientQuotientModelIso (I : Ideal A)
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X)).obj ≅
      DerivedCategory.Q.obj (baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex)) :=
  boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk I) _
    (deltaRootSourceCoefficientModel X P)

end SerrePositivity.BhattScholze

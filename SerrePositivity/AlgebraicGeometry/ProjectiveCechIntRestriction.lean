module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
概要：任意の宇宙の係数環の Čech 複体を整数加群として比較する。
方針：各項の恒等写像と、整数への係数制限の完全性を使う。
規約：整数環の宇宙を係数環の宇宙に固定しない。
使われ方：Frobenius の反復を整数線形な複体の自己射として追跡する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
variable {ι : Type} [DecidableEq ι] (D : Finset ι ⥤ ModuleCat.{u} R)

/-- Čech 複体の形成は整数加群への係数制限と交換する。 -/
def projectiveCechIntRestrictionComplexIso :
    fullCechComplex (D ⋙ ModuleCat.restrictScalars (Int.castRingHom R)) ≅
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex (.up ℕ)).obj
        (fullCechComplex D) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ LinearEquiv.toModuleIso
      ({ toFun := fun x ↦ x
         invFun := fun x ↦ x
         left_inv := fun _ ↦ rfl
         right_inv := fun _ ↦ rfl
         map_add' := fun _ _ ↦ rfl
         map_smul' := fun _ _ ↦ rfl } :
        (fullCechComplex (D ⋙ ModuleCat.restrictScalars (Int.castRingHom R))).X q ≃ₗ[ℤ]
        (((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex (.up ℕ)).obj
          (fullCechComplex D)).X q))
    (by
      intro i j hij
      have h : i + 1 = j := hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((ModuleCat.restrictScalars (Int.castRingHom R)).map
        ((fullCechComplex D).d i (i + 1))).hom x =
        ((fullCechComplex (D ⋙ ModuleCat.restrictScalars (Int.castRingHom R))).d i (i + 1)).hom x
      simp only [fullCechComplex, CochainComplex.of_d]
      change fullCechDifferential D (i + 1) x =
        fullCechDifferential (D ⋙ ModuleCat.restrictScalars (Int.castRingHom R)) (i + 1) x
      funext t
      simp only [fullCechDifferential_apply]
      rfl)

/-- Čech H の整数加群への係数制限との比較。
BST13 Lemma 3.9 の Hⁱ の Frobenius 順極限に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveCechIntRestrictionHomologyIso (q : ℕ) :
    (fullCechComplex (D ⋙ ModuleCat.restrictScalars (Int.castRingHom R))).homology q ≅
      (ModuleCat.restrictScalars (Int.castRingHom R)).obj ((fullCechComplex D).homology q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).mapIso
    (projectiveCechIntRestrictionComplexIso D) ≪≫
      ((fullCechComplex D).sc q).mapHomologyIso (ModuleCat.restrictScalars (Int.castRingHom R))

/-- 整数係数への複体比較は、係数図式の射に自然。 -/
@[reassoc]
theorem projectiveCechIntRestrictionComplexIso_naturality
    {D E : Finset ι ⥤ ModuleCat.{u} R} (η : D ⟶ E) :
    fullCechComplexMap (Functor.whiskerRight η (ModuleCat.restrictScalars (Int.castRingHom R))) ≫
        (projectiveCechIntRestrictionComplexIso E).hom =
      (projectiveCechIntRestrictionComplexIso D).hom ≫
        ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex (.up ℕ)).map
          (fullCechComplexMap η) := by
  ext q x
  rfl

/-- 整数係数への Čech H の比較は、係数図式の射に自然。
BST13 Lemma 3.9 の Hⁱ の制限に用いる Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
@[reassoc]
theorem projectiveCechIntRestrictionHomologyIso_naturality
    {D E : Finset ι ⥤ ModuleCat.{u} R} (η : D ⟶ E) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
        (fullCechComplexMap
          (Functor.whiskerRight η (ModuleCat.restrictScalars (Int.castRingHom R)))) ≫
        (projectiveCechIntRestrictionHomologyIso E q).hom =
      (projectiveCechIntRestrictionHomologyIso D q).hom ≫
        (ModuleCat.restrictScalars (Int.castRingHom R)).map
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
            (fullCechComplexMap η)) := by
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  let HR := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let bD := ((fullCechComplex D).sc q).mapHomologyIso F
  let bE := ((fullCechComplex E).sc q).mapHomologyIso F
  have hb : H.map ((F.mapHomologicalComplex (.up ℕ)).map (fullCechComplexMap η)) ≫
      bE.hom = bD.hom ≫ F.map (HR.map (fullCechComplexMap η)) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap η)) F
  change H.map (fullCechComplexMap (Functor.whiskerRight η F)) ≫
      (H.map (projectiveCechIntRestrictionComplexIso E).hom ≫ bE.hom) =
    (H.map (projectiveCechIntRestrictionComplexIso D).hom ≫ bD.hom) ≫
      F.map (HR.map (fullCechComplexMap η))
  rw [← H.map_comp_assoc, projectiveCechIntRestrictionComplexIso_naturality,
    H.map_comp_assoc, hb]
  simp only [Category.assoc]

end SerrePositivity.AlgebraicGeometry

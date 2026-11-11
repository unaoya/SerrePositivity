module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechRestrictScalars
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：Čech 版の係数制限の比較を、係数図式の写像に自然なものにする。
方針：複体では各タプルの成分を比較し、コホモロジーでは Mathlib の自然性を使う。
規約：被覆の添字は固定し、任意の係数の自然変換を許す。
使われ方：原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 比較と作用の追跡。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
variable {ι : Type} [DecidableEq ι] {D E : Finset ι ⥤ ModuleCat.{u} B}

/-- Čech 複体の係数制限の比較は、係数の自然変換と可換。 -/
@[reassoc]
theorem projectiveCechRestrictScalarsComplexIso_naturality (η : D ⟶ E) :
    fullCechComplexMap (Functor.whiskerRight η (ModuleCat.restrictScalars φ)) ≫
        (projectiveCechRestrictScalarsComplexIso φ E).hom =
      (projectiveCechRestrictScalarsComplexIso φ D).hom ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).map
          (fullCechComplexMap η) := by
  ext q x
  rfl

/-- Čech 版のコホモロジーと係数制限の比較は、係数の自然変換に自然。
原典 Stacks 30.20.1 の Hⁱ と Rees 作用に対応する Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
@[reassoc]
theorem projectiveCechRestrictScalarsHomologyIso_naturality (η : D ⟶ E) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (Functor.whiskerRight η (ModuleCat.restrictScalars φ))) ≫
        (projectiveCechRestrictScalarsHomologyIso φ E q).hom =
      (projectiveCechRestrictScalarsHomologyIso φ D q).hom ≫
        (ModuleCat.restrictScalars φ).map
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
            (fullCechComplexMap η)) := by
  let F := ModuleCat.restrictScalars φ
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let HB := HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q
  let bD := ((fullCechComplex D).sc q).mapHomologyIso F
  let bE := ((fullCechComplex E).sc q).mapHomologyIso F
  have hb : H.map ((F.mapHomologicalComplex (.up ℕ)).map (fullCechComplexMap η)) ≫
      bE.hom = bD.hom ≫ F.map (HB.map (fullCechComplexMap η)) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (.up ℕ) q).map
        (fullCechComplexMap η)) F
  change H.map (fullCechComplexMap (Functor.whiskerRight η F)) ≫
      (H.map (projectiveCechRestrictScalarsComplexIso φ E).hom ≫ bE.hom) =
    (H.map (projectiveCechRestrictScalarsComplexIso φ D).hom ≫ bD.hom) ≫
      F.map (HB.map (fullCechComplexMap η))
  rw [← H.map_comp_assoc, projectiveCechRestrictScalarsComplexIso_naturality,
    H.map_comp_assoc, hb]
  simp only [Category.assoc]

end SerrePositivity.AlgebraicGeometry

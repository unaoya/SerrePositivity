module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechTensorNaturality
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：有限被覆の Čech コホモロジーと、flat なテンソル底変換を比較する。
方針：テンソル底変換の完全性と、既存の複体の比較同型を合成する。
規約：原典 Stacks 30.5.2(2) の Hⁱ に対応する Čech 版。
使われ方：射影的な標準開の計算に、flat な係数拡大を接続する。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
variable {ι : Type} [DecidableEq ι] [Fintype ι]
local instance projectiveCechFlatExtendAdditive : (ModuleCat.extendScalars φ).Additive :=
  projectiveCechTensorExtendAdditive φ
variable (D : Finset ι ⥤ ModuleCat.{u} R)

/-- flat なテンソル底変換は、有限被覆の Čech コホモロジーと交換する。
原典 Stacks 30.5.2(2) の Hⁱ の flat 底変換の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveCechFlatBaseChangeIso (hφ : φ.Flat) (q : ℕ) :
    (ModuleCat.extendScalars φ).obj ((fullCechComplex D).homology q) ≅
      (fullCechComplex (D ⋙ ModuleCat.extendScalars φ)).homology q := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact (((fullCechComplex D).sc q).mapHomologyIso (ModuleCat.extendScalars φ)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).mapIso
      (projectiveCechTensorComplexIso φ D)

/-- flat な Čech 底変換の比較は、係数図式の任意の射に自然。
原典 Stacks 30.5.2(2) の Hⁱ の底変換の自然性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechFlatBaseChangeIso_naturality (hφ : φ.Flat)
    (E : Finset ι ⥤ ModuleCat.{u} R) (η : D ⟶ E) (q : ℕ) :
    (ModuleCat.extendScalars φ).map
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
          (fullCechComplexMap η)) ≫ (projectiveCechFlatBaseChangeIso φ E hφ q).hom =
      (projectiveCechFlatBaseChangeIso φ D hφ q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
          (fullCechComplexMap (Functor.whiskerRight η (ModuleCat.extendScalars φ))) := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  let F := ModuleCat.extendScalars φ
  let HR := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let HB := HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q
  let bD := ((fullCechComplex D).sc q).mapHomologyIso F
  let bE := ((fullCechComplex E).sc q).mapHomologyIso F
  have hb : HB.map ((F.mapHomologicalComplex (.up ℕ)).map (fullCechComplexMap η)) ≫
      bE.hom = bD.hom ≫ F.map (HR.map (fullCechComplexMap η)) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap η)) F
  have hbi : F.map (HR.map (fullCechComplexMap η)) ≫ bE.inv =
      bD.inv ≫ HB.map ((F.mapHomologicalComplex (.up ℕ)).map (fullCechComplexMap η)) := by
    apply (cancel_mono bE.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hb]
    simp only [Iso.inv_hom_id_assoc]
  have hc := congrArg (fun f ↦ HB.map f) (projectiveCechTensorComplexIso_naturality φ D E η)
  simp only [Functor.map_comp] at hc
  change F.map (HR.map (fullCechComplexMap η)) ≫
      (bE.inv ≫ HB.map (projectiveCechTensorComplexIso φ E).hom) =
    (bD.inv ≫ HB.map (projectiveCechTensorComplexIso φ D).hom) ≫
      HB.map (fullCechComplexMap (Functor.whiskerRight η F))
  rw [← Category.assoc, hbi, Category.assoc, hc]
  simp only [Category.assoc, F]

/-- flat 底変換後の Čech コホモロジーは、元のコホモロジーの有限生成性を保つ。
原典 Stacks 30.5.2(2) の Hⁱ の比較からの有限性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechFlatBaseChange_finite (hφ : φ.Flat) (q : ℕ)
    [Module.Finite R ((fullCechComplex D).homology q)] :
    Module.Finite B ((fullCechComplex (D ⋙ ModuleCat.extendScalars φ)).homology q) := by
  letI := φ.toAlgebra
  letI : Module.Finite B ((ModuleCat.extendScalars φ).obj ((fullCechComplex D).homology q)) :=
    inferInstanceAs (Module.Finite B (B ⊗[R] ((fullCechComplex D).homology q)))
  exact Module.Finite.equiv (projectiveCechFlatBaseChangeIso φ D hφ q).toLinearEquiv

end SerrePositivity.AlgebraicGeometry

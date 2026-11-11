module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechDirectSumHomology
public import SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumHomologyInclusion

/-!
概要：Čech 版の直和コホモロジー比較と各成分の包含との両立性。
方針：項ごとの包含を短複体へ写し、直和の包含の公式を適用する。
規約：原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の比較である。
使われ方：Rees 単項式が次数を動かす作用を、Čech コホモロジーへ移す。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped DirectSum
universe u
variable {R : Type u} [CommRing R] {κ ι : Type} [DecidableEq κ] [DecidableEq ι] [Fintype ι]
variable (D : κ → Finset ι ⥤ ModuleCat.{u} R)

/-- Čech 複体の各成分から項ごとの直和への包含。 -/
def projectiveCechDirectSumComplexInclusion (n : κ) :
    fullCechComplex (D n) ⟶ projectiveCechDirectSumComplex D where
  f q := ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ (fullCechComplex (D n)).X q) n)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, projectiveCechDirectSumComplex_d]
    apply LinearMap.ext
    intro x
    exact DirectSum.lmap_lof (fun n ↦ ((fullCechComplex (D n)).d i j).hom) n x

/-- 係数の直和の Čech 複体への、各成分の包含。 -/
def projectiveCechDirectSumInclusion (n : κ) :
    fullCechComplex (D n) ⟶ fullCechComplex (projectiveCechDirectSumDiagram D) :=
  projectiveCechDirectSumComplexInclusion D n ≫ (projectiveCechDirectSumComplexIso D).hom

/-- Čech 版の直和コホモロジー比較は各成分の包含を保つ。
原典 Stacks 30.20.1 の Hⁱ の直和と Rees 作用の比較に使う。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechDirectSumHomologyIso_inclusion (q : ℕ) (n : κ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (projectiveCechDirectSumInclusion D n) ≫
      (projectiveCechDirectSumHomologyIso D q).hom =
        ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ (fullCechComplex (D n)).homology q) n) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let t := projectiveCechDirectSumComplexIso D
  let a := projectiveCechDirectSumShortComplexIso D q
  let b := projectiveDirectSumShortComplexHomologyIso (fun n ↦ (fullCechComplex (D n)).sc q)
  rw [projectiveCechDirectSumInclusion, H.map_comp]
  change (H.map (projectiveCechDirectSumComplexInclusion D n) ≫ (H.mapIso t).hom) ≫
    ((H.mapIso t).inv ≫ (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map a.hom ≫ b.hom) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map
    (((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q).map
      (projectiveCechDirectSumComplexInclusion D n))) ≫
      (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map a.hom ≫ b.hom = _
  rw [← Functor.map_comp_assoc]
  have h : ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q).map
      (projectiveCechDirectSumComplexInclusion D n)) ≫ a.hom =
      projectiveDirectSumShortComplexInclusion (fun n ↦ (fullCechComplex (D n)).sc q) n := by
    apply ShortComplex.hom_ext <;> exact Category.comp_id _
  rw [h]
  exact projectiveDirectSumShortComplexHomologyIso_inclusion _ n

end SerrePositivity.AlgebraicGeometry

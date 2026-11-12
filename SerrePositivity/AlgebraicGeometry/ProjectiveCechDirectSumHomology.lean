module

public import SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumCech
public import SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumHomology

/-!
概要：射影標準開の Čech 版のコホモロジーと、係数の任意直和の交換。
方針：項ごとの同型と、短複体の直和のコホモロジー比較を合成する。
規約：これは Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の比較である。
使われ方：Rees 次数ごとの Čech コホモロジーを、全 Rees 加群の計算へつなぐ。
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

/-- 項ごとの直和の余境界は、各複体の余境界の直和。 -/
theorem projectiveCechDirectSumComplex_d (i j : ℕ) :
    ((projectiveCechDirectSumComplex D).d i j).hom =
      DirectSum.lmap (fun n ↦ ((fullCechComplex (D n)).d i j).hom) := by
  by_cases h : i + 1 = j
  · subst j
    simp only [projectiveCechDirectSumComplex, fullCechComplex, CochainComplex.of_d,
      ModuleCat.hom_ofHom]
  · rw [(projectiveCechDirectSumComplex D).shape i j h]
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro n
    change 0 = ((fullCechComplex (D n)).d i j).hom
      ((DirectSum.component R κ (fun n ↦ (fullCechComplex (D n)).X i) n) x)
    rw [(fullCechComplex (D n)).shape i j h]
    rfl

/-- 直和の複体の三項を、三項の直和と比較する。 -/
def projectiveCechDirectSumShortComplexIso (q : ℕ) :
    (projectiveCechDirectSumComplex D).sc q ≅
      projectiveDirectSumShortComplex (fun n ↦ (fullCechComplex (D n)).sc q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    exact (projectiveCechDirectSumComplex_d D _ _).symm) (by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    exact (projectiveCechDirectSumComplex_d D _ _).symm)

/-- 射影標準開の Čech 版のコホモロジーは、係数の直和と交換する。
原典 Stacks 30.20.1 の Hⁱ の直和を扱うための Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveCechDirectSumHomologyIso (q : ℕ) :
    (fullCechComplex (projectiveCechDirectSumDiagram D)).homology q ≅
      ModuleCat.of R (⨁ n, (fullCechComplex (D n)).homology q) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    (projectiveCechDirectSumComplexIso D)).symm ≪≫
    (ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso
      (projectiveCechDirectSumShortComplexIso D q) ≪≫
    projectiveDirectSumShortComplexHomologyIso (fun n ↦ (fullCechComplex (D n)).sc q)

end SerrePositivity.AlgebraicGeometry

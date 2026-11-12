module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
概要：Čech 版の複体とコホモロジーの計算は、係数環の作用の制限と交換する。
方針：各タプルの成分の恒等同型と、係数制限の完全性を使う。
規約：これは係数制限であり、テンソル積による底変換ではない。
使われ方：Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 比較で、基底環上の比較から
Rees 環上の有限性を移す。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
variable {ι : Type} [DecidableEq ι] (D : Finset ι ⥤ ModuleCat.{u} B)

/-- Čech 複体の形成は、係数環の作用の制限と交換する。 -/
def projectiveCechRestrictScalarsComplexIso :
    fullCechComplex (D ⋙ ModuleCat.restrictScalars φ) ≅
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj (fullCechComplex D) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (LinearEquiv.refl R (FullCechCochains (D ⋙ ModuleCat.restrictScalars φ) (q + 1))).toModuleIso)
    (by
      intro i j hij
      have h : i + 1 = j := hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((ModuleCat.restrictScalars φ).map ((fullCechComplex D).d i (i + 1))).hom x =
        ((fullCechComplex (D ⋙ ModuleCat.restrictScalars φ)).d i (i + 1)).hom x
      simp only [fullCechComplex, CochainComplex.of_d]
      change fullCechDifferential D (i + 1) x =
        fullCechDifferential (D ⋙ ModuleCat.restrictScalars φ) (i + 1) x
      funext t
      simp only [fullCechDifferential_apply]
      rfl)

/-- Čech 版のコホモロジーは係数制限と交換する。
原典 Stacks 30.20.1 の Hⁱ に対応する Rees–Čech 比較に使う。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveCechRestrictScalarsHomologyIso (q : ℕ) :
    (fullCechComplex (D ⋙ ModuleCat.restrictScalars φ)).homology q ≅
      (ModuleCat.restrictScalars φ).obj ((fullCechComplex D).homology q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    (projectiveCechRestrictScalarsComplexIso φ D) ≪≫
      ((fullCechComplex D).sc q).mapHomologyIso (ModuleCat.restrictScalars φ)

end SerrePositivity.AlgebraicGeometry

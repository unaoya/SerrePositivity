module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechDirectSumInclusion
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：係数図式の各成分からの包含と、既存の Čech 直和包含を比較する。
方針：各タプルの係数で、直和と有限積を交換する同値の公式を使う。
規約：被覆添字は有限で、直和の添字に有限性を要求しない。
使われ方：Rees の chart の包含の公式を、Čech コホモロジーへ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R : Type u} [CommRing R] {κ ι : Type} [DecidableEq κ] [DecidableEq ι] [Fintype ι]
variable (D : κ → Finset ι ⥤ ModuleCat.{u} R)

/-- 各係数図式から、係数の直和の図式への包含。 -/
def projectiveCechDirectSumDiagramInclusion (i : κ) : D i ⟶ projectiveCechDirectSumDiagram D where
  app T := ModuleCat.ofHom (DirectSum.lof R κ (fun j ↦ (D j).obj T) i)
  naturality {T U} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (DirectSum.lmap_lof (fun j ↦ ((D j).map h).hom) i x).symm

/-- 係数図式の包含が誘導する Čech 写像は、項ごとの直和からの既存の包含に一致。 -/
theorem projectiveCechDirectSumDiagramInclusion_complex (i : κ) :
    fullCechComplexMap (projectiveCechDirectSumDiagramInclusion D i) =
      projectiveCechDirectSumInclusion D i := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext t
  apply DFinsupp.ext
  intro j
  change (DirectSum.lof R κ (fun n ↦ (D n).obj (cechTupleSupport t)) i (x t)) j =
    (DirectSum.lof R κ (fun n ↦ FullCechCochains (D n) (q + 1)) i x) j t
  by_cases h : j = i
  · subst j
    simp only [DirectSum.lof_apply]
  · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne (β := fun n ↦ (D n).obj (cechTupleSupport t)) i j (x t) h,
      DirectSum.of_eq_of_ne (β := fun n ↦ FullCechCochains (D n) (q + 1)) i j x h, Pi.zero_apply]

/-- 係数図式の包含についての Čech コホモロジーの直和比較の公式。
原典 Stacks 30.20.1 の Hⁱ の直和比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechDirectSumDiagramInclusion_homology (i : κ) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (projectiveCechDirectSumDiagramInclusion D i)) ≫
      (projectiveCechDirectSumHomologyIso D q).hom =
    ModuleCat.ofHom (DirectSum.lof R κ
      (fun j ↦ (fullCechComplex (D j)).homology q) i) := by
  rw [projectiveCechDirectSumDiagramInclusion_complex]
  exact projectiveCechDirectSumHomologyIso_inclusion D q i

end SerrePositivity.AlgebraicGeometry

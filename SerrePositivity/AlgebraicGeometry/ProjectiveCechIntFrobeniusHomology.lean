module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFrobenius
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
概要：実際の標準開 Čech H の Frobenius の有向系を作る。
方針：整数線形な図式の反復則をコホモロジー関手で移す。
規約：捻り零で同じ群を各段に置き、段差 e の写像は p^e 乗から誘導する。
使われ方：F6 の正次数の比較と F7 の次数零の比較の共通の順極限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [DecidableEq ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 捻り零の標準開の Čech H を整数加群として読む。
BST13 Lemma 3.9 の Hⁱ に用いる Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
abbrev ProjectiveCechIntHomology (q : ℕ) :=
  (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G 0 ⋙
    ModuleCat.restrictScalars (Int.castRingHom R))).homology q

/-- 実際の標準開の p^e 乗から誘導される Čech H の反復 Frobenius。 -/
def projectiveCechIntFrobeniusHomology (e q : ℕ) :
    ProjectiveCechIntHomology (ι := ι) G q →ₗ[ℤ] ProjectiveCechIntHomology (ι := ι) G q :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
    (fullCechComplexMap (projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA e))).hom

/-- Čech H 上の零回の反復は恒等写像。 -/
theorem projectiveCechIntFrobeniusHomology_zero (q : ℕ) :
    projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA 0 q = LinearMap.id := by
  let H : (Finset ι ⥤ ModuleCat.{u} ℤ) ⥤ ModuleCat.{u} ℤ := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  change (H.map (projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA 0)).hom = _
  rw [projectiveCechIntFrobeniusDiagram_zero, H.map_id]
  rfl

/-- Čech H 上で反復回数の加法は写像の合成になる。 -/
theorem projectiveCechIntFrobeniusHomology_add (e f q : ℕ) :
    projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (e + f) q =
      (projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA f q).comp
        (projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA e q) := by
  let H : (Finset ι ⥤ ModuleCat.{u} ℤ) ⥤ ModuleCat.{u} ℤ := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  change (H.map (projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA (e + f))).hom = _
  rw [projectiveCechIntFrobeniusDiagram_add, H.map_comp]
  rfl

/-- 実際の Čech H の反復 Frobenius は、自然数段の有向系を与える。 -/
instance projectiveCechIntFrobeniusHomology_directedSystem (q : ℕ) :
    DirectedSystem (fun _ : ℕ ↦ ProjectiveCechIntHomology (ι := ι) G q)
      (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q) where
  map_self {i} x := by
    rw [Nat.sub_self, projectiveCechIntFrobeniusHomology_zero]
    rfl
  map_map {k j i} hij hjk x := by
    have hsum : j - i + (k - j) = k - i := by omega
    have h := congrArg (fun f ↦ f x)
      (projectiveCechIntFrobeniusHomology_add (ι := ι) G p hp hR hA (j - i) (k - j) q)
    simpa only [hsum, LinearMap.comp_apply] using h.symm

end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.AlgebraicGeometry.LinearDirectLimitCocone
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusDirectLimit

/-!
概要：標準開の Frobenius 系を関手としてまとめ、その H の余極限を比較する。
方針：段差の反復を実際の遷移に使い、代数的順極限の普遍性へ渡す。
規約：整数係数は加法群の表示であり、元の係数の宇宙を制限しない。
使われ方：F6 の H の順極限と perfection の Čech 複体の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 各標準開で実際の Frobenius の反復を取る自然数の係数図式。 -/
def projectiveCechFrobeniusCoefficientFunctor : ℕ ⥤ Finset ι ⥤ ModuleCat.{u} ℤ where
  obj _ := projectiveNatGradedModuleChartDiagram (ι := ι) G 0 ⋙
    ModuleCat.restrictScalars (Int.castRingHom R)
  map {i j} _ := projectiveCechIntFrobeniusDiagram G p hp hR hA (j - i)
  map_id _ := by simp only [Nat.sub_self, projectiveCechIntFrobeniusDiagram_zero]
  map_comp {i j k} h l := by
    have hij := leOfHom h
    have hjk := leOfHom l
    have he : k - i = (j - i) + (k - j) := by omega
    rw [he, projectiveCechIntFrobeniusDiagram_add]

/-- Frobenius の各段の Čech H は、代数的順極限に使った同じ有向系を与える。
BST13 Lemma 3.9 の Hⁱ に用いる Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
def projectiveCechFrobeniusHomologyDiagramIso (q : ℕ) :
    projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA ⋙
        fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q ≅
      linearDirectSystemFunctor
        (fun i j (_h : i ≤ j) ↦
          projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j h
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    rfl)

/-- 実際の Frobenius 順極限と、各段の Čech H の圏論的余極限の同型。 -/
def projectiveCechFrobeniusHomologyColimitIso (q : ℕ) :
    ModuleCat.of ℤ (ProjectiveCechFrobeniusDirectLimit (ι := ι) G p hp hR hA q) ≅
      colimit (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA ⋙
        fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) :=
  by
    let e := linearDirectLimitColimitIso
      (fun i j (_h : i ≤ j) ↦
        projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q)
    let b : ModuleCat.of ℤ
        (ProjectiveCechFrobeniusDirectLimit (ι := ι) G p hp hR hA q) ≅
        (linearDirectSystemCocone
          (fun i j (_h : i ≤ j) ↦
            projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q)).pt :=
      LinearEquiv.toModuleIso
        ((AddEquiv.refl
          (ProjectiveCechFrobeniusDirectLimit (ι := ι) G p hp hR hA q)).toIntLinearEquiv)
    exact b ≪≫ e ≪≫
      (colim (J := ℕ)).mapIso
        (projectiveCechFrobeniusHomologyDiagramIso (ι := ι) G p hp hR hA q).symm

end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjAdicCechProjection
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechCompletion
public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamiliesEquiv

/-!
概要：実際の閉厚化の Čech コホモロジーと Rees の商を I 進遷移ごと比較する。
方針：複体の自然な同型に homology を適用し、互換族に移す。
規約：すべて Čech 版。導来関手のコホモロジーとの比較は行わない。
使われ方：実際の閉厚化に対する Čech 形式関数。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (I : Ideal R) (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 実際の閉厚化の標準開被覆による Čech コホモロジー。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
abbrev projectiveProjAdicCechHomology (n q : ℕ) :=
  (projectiveProjAdicCechComplex (ι := ι) I G n).homology q

/-- 実際の厚化間の射が誘導する Čech コホモロジーの遷移。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjAdicCechHomologyTransition (i j : ℕ) (h : j ≤ i) (q : ℕ) :
    projectiveProjAdicCechHomology (ι := ι) I G i q ⟶
      projectiveProjAdicCechHomology (ι := ι) I G j q :=
  HomologicalComplex.homologyMap (projectiveProjAdicCechTransition (ι := ι) I G i j h) q

/-- 元の構造層から実際の閉厚化への Čech コホモロジーの射影。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjAdicCechHomologyProjection (n q : ℕ) :=
  HomologicalComplex.homologyMap (projectiveProjAdicCechProjection (ι := ι) I G n) q

/-- 元の Proj の構造層の標準開 Čech コホモロジー。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
abbrev projectiveProjSourceCechHomology (q : ℕ) :=
  (fullCechComplex (openCoverCechDiagram
    (schemeStructureCechPresheaf (_root_.AlgebraicGeometry.Proj G) ⋙
      ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
        (projectiveProjCechOpen (ι := ι) G))).homology q

/-- 元の Proj の標準開被覆の Čech H と、次数零の計算の同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjSourceCechHomologyIso (q : ℕ) :
    reesAdicProjectiveCechTarget (ι := ι) G 0 q ≅
      projectiveProjSourceCechHomology (ι := ι) G q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    (projectiveProjNativeNatCechComplexIso (ι := ι) G)

/-- 実際の閉厚化の Čech H と、Rees の商による計算の同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjAdicCechHomologyIso (n q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I G n 0 q ≅
      projectiveProjAdicCechHomology (ι := ι) I G n q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    (projectiveProjAdicCechComplexIso (ι := ι) I G n)

/-- 閉厚化の Čech H の比較は I 進遷移と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveProjAdicCechHomologyIso_transition (i j : ℕ) (h : j ≤ i) (q : ℕ) :
    reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h 0 q ≫
        (projectiveProjAdicCechHomologyIso (ι := ι) I G j q).hom =
      (projectiveProjAdicCechHomologyIso (ι := ι) I G i q).hom ≫
        projectiveProjAdicCechHomologyTransition (ι := ι) I G i j h q := by
  have hm := congrArg
    (fun f ↦ (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map f)
    (projectiveProjAdicCechComplexIso_transition (ι := ι) I G i j h)
  simpa only [projectiveProjAdicCechHomologyIso, projectiveProjSourceCechHomologyIso,
    projectiveProjAdicCechHomologyTransition, projectiveProjAdicCechHomologyProjection,
    reesAdicProjectiveClosedCechTransition, reesAdicProjectiveClosedCechProjection,
    Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] using hm

/-- 閉厚化の Čech H の比較は、元の構造層からの射影と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveProjAdicCechHomologyIso_projection (n q : ℕ) :
    reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 q ≫
        (projectiveProjAdicCechHomologyIso (ι := ι) I G n q).hom =
      (projectiveProjSourceCechHomologyIso (ι := ι) G q).hom ≫
        projectiveProjAdicCechHomologyProjection (ι := ι) I G n q := by
  have hm := congrArg
    (fun f ↦ (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map f)
    (projectiveProjAdicCechComplexIso_projection (ι := ι) I G n)
  simpa only [projectiveProjAdicCechHomologyIso, projectiveProjSourceCechHomologyIso,
    projectiveProjAdicCechHomologyTransition, projectiveProjAdicCechHomologyProjection,
    reesAdicProjectiveClosedCechTransition, reesAdicProjectiveClosedCechProjection,
    Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] using hm

/-- 実際の閉厚化の Čech コホモロジーの互換族。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjAdicCechFamilies (q : ℕ) :=
  compatibleLinearFamilies
    (fun i j h ↦ (projectiveProjAdicCechHomologyTransition (ι := ι) I G i j h q).hom)

/-- Rees の商の互換族と、実際の閉厚化の Čech 互換族の線形同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjAdicCechFamiliesEquiv (q : ℕ) :
    reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G 0 q ≃ₗ[R]
      projectiveProjAdicCechFamilies (ι := ι) I G q :=
  compatibleLinearFamiliesEquiv _ _
    (fun n ↦ (projectiveProjAdicCechHomologyIso (ι := ι) I G n q).toLinearEquiv)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (projectiveProjAdicCechHomologyIso_transition (ι := ι) I G i j h q).symm)

end SerrePositivity.AlgebraicGeometry

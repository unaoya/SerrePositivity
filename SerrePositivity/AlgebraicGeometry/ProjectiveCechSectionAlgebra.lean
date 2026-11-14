module

public import SerrePositivity.AlgebraicGeometry.SchemeSectionAlgebraCech
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechFiniteness

/-!
概要：射影スキームの標準開の適合する切断の代数と、その有限性。
方針：実際の構造層の Čech H⁰ との同型で射影有限性を移す。
規約：代数の乗法は各標準開の切断環の乗法。
使われ方：BST13 の次数零の四角形で有限環拡大として扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 実際の Proj の標準開の適合する切断の部分代数。 -/
abbrev projectiveCechSectionAlgebra :=
  fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram (Proj G)
    (projectiveScalarToGlobalSections G) (projectiveProjCechOpen (ι := ι) G))

/-- 標準開の切断の部分代数は基底環上有限。BST13 Lemma 3.8 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechSectionAlgebra_finite
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S] :
    Module.Finite R (projectiveCechSectionAlgebra (ι := ι) G) := by
  letI := projectiveProjNativeStandardCechHomology_finite (ι := ι) G 0
  let e := schemeSectionAlgebraCechH0Equiv (Proj G) (projectiveScalarToGlobalSections G)
    (projectiveProjCechOpen (ι := ι) G)
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.AlgebraicGeometry.CechScalarCokernelSupport
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionAlgebra
public import SerrePositivity.AlgebraicGeometry.FiniteSupportConductor

/-!
概要：射影標準開の切断部分代数のスカラー余核を中心の冪で消す。
方針：中心外での実際の底変換と、射影の次数零の有限性を合成する。
規約：切断部分代数のスカラー写像と、その実際の余核を使う。
使われ方：BST13 Lemma 3.9 の次数零の導手の評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]


variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))))
variable (I : Ideal R)
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]

include hspan in
/-- 射影標準開の切断部分代数のスカラー余核の台は中心内。
BST13 Lemma 3.9 の次数零で使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechScalarCokernel_support :
    Module.support R (projectiveCechSectionAlgebra (ι := ι) G ⧸
      LinearMap.range (Algebra.linearMap R (projectiveCechSectionAlgebra (ι := ι) G))) ⊆
        PrimeSpectrum.zeroLocus (I : Set R) := by
  have hs := schemeCechScalarCokernel_support_subset_of_isoOffCenter
    (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) I
    (projectiveProjCechOpen (ι := ι) G)
    (fun i ↦ Proj.isAffineOpen_basicOpen G _ (projectivePolynomialVariableImage_mem G i)
      Nat.zero_lt_one)
    (Proj.iSup_basicOpen_eq_top G _ hspan)
  let B (φ : R →+* Γ(Proj G, ⊤)) := fullAlgebraCechEqualizer
    (schemeSectionAlgebraCechDiagram (Proj G) φ (projectiveProjCechOpen (ι := ι) G))
  exact Eq.mp (congrArg (fun φ : R →+* Γ(Proj G, ⊤) ↦
    Module.support R (B φ ⧸ LinearMap.range (Algebra.linearMap R (B φ))) ⊆
      PrimeSpectrum.zeroLocus (I : Set R))
    (schemeScalarHom_scalarMorphism (Proj G) (projectiveScalarToGlobalSections G))) hs

include hspan in
/-- 射影の次数零の切断代数のスカラー余核は、中心のある冪で消える。
BST13 Lemma 3.9 の次数零の評価の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechScalarCokernel_power_annihilates :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R
      (projectiveCechSectionAlgebra (ι := ι) G ⧸
        LinearMap.range (Algebra.linearMap R (projectiveCechSectionAlgebra (ι := ι) G))) := by
  letI := projectiveCechSectionAlgebra_finite (ι := ι) G
  exact finiteSupport_exists_pow_le_annihilator _ I (Ideal.fg_of_isNoetherianRing I)
    (projectiveCechScalarCokernel_support G hspan I)

include hspan in
/-- 中心の十分高い冪を切断代数へ拡大したイデアルの元は、基底環に持ち上がる。 -/
theorem projectiveCechSectionAlgebra_exists_pow_map_lift :
    ∃ n : ℕ, ∀ b ∈ (I ^ n).map (algebraMap R (projectiveCechSectionAlgebra (ι := ι) G)),
      ∃ a : R, algebraMap R (projectiveCechSectionAlgebra (ι := ι) G) a = b := by
  letI := projectiveCechSectionAlgebra_finite (ι := ι) G
  exact finiteSupport_exists_pow_map_lift I (Ideal.fg_of_isNoetherianRing I)
    (projectiveCechScalarCokernel_support G hspan I)

end SerrePositivity.AlgebraicGeometry

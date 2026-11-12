module

public import SerrePositivity.AlgebraicGeometry.CechSupportOutsideCenter
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechFiniteness

/-!
概要：中心外で同型な射影スキームの正次数 Čech H を、中心のある冪で消す。
方針：実際の同型な局所化から台を制御し、射影有限性を使う。
規約：構造射は標準開の計算に使った大域スカラーから定める。
使われ方：BST13 Lemma 3.9 の正次数の評価。
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

/-- 中心外で同型な射影スキームの正次数 Čech H は中心のある冪で消える。
BST13 Lemma 3.9 の正次数の評価に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechSupport_power_annihilates
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S]
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))))
    (I : Ideal R)
    [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
      affineCenterComplement I)] (q : ℕ) (hq : 0 < q) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R
      ((fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
          (projectiveProjCechOpen (ι := ι) G))).homology q) := by
  letI := projectiveProjNativeStandardCechHomology_finite (ι := ι) G q
  apply finiteSupport_exists_pow_le_annihilator _ I (Ideal.fg_of_isNoetherianRing I)
  have hs := schemeCechSupport_subset_of_isoOffCenter
    (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) I
    (projectiveProjCechOpen (ι := ι) G)
    (fun i ↦ Proj.isAffineOpen_basicOpen G _ (projectivePolynomialVariableImage_mem G i)
      Nat.zero_lt_one)
    (Proj.iSup_basicOpen_eq_top G _ hspan) q hq
  exact Eq.mp (congrArg (fun φ : R →+* Γ(Proj G, ⊤) ↦
    Module.support R ((fullCechComplex (openCoverCechDiagram
      (schemeStructureCechPresheaf (Proj G) ⋙ ModuleCat.restrictScalars φ)
        (projectiveProjCechOpen (ι := ι) G))).homology q) ⊆
      PrimeSpectrum.zeroLocus (I : Set R))
    (schemeScalarHom_scalarMorphism (Proj G) (projectiveScalarToGlobalSections G))) hs

end SerrePositivity.AlgebraicGeometry

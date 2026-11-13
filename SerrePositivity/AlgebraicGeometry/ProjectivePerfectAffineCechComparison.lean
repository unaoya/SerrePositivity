module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechComparison

/-!
概要：F8 の固定した斉次局所化での Čech H を、任意の有限アフィン被覆での計算へ渡す。
方針：非空交叉の実際の切断への同型と、Frobenius 後の共通アフィン比較を合成する。
規約：被覆比較の同型性を追加仮定にせず、アフィン性と被覆性から供給する。
使われ方：射影四角形の計算を、2g の細分の選択によらない形へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- F8 の固定した複体の Čech H と、任意の有限アフィン被覆の実際の Frobenius 係数での比較。
BST13 Lemma 3.9 と Stacks 30.2.6 の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectivePerfectAffineCechHomologyIso
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
    {κ : Type} [LinearOrder κ] [Fintype κ]
    (V : κ → (Proj G).Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hcV : (⨆ j, V j) = ⊤) (q : ℕ) :
    (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).homology q ≅
      (fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
        V)).homology q := by
  let U := projectiveProjCechOpen (ι := ι) G
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦
    Proj.isAffineOpen_basicOpen G _ (projectivePolynomialVariableImage_mem G i) Nat.zero_lt_one
  have hcU : (⨆ i, U i) = ⊤ := Proj.iSup_basicOpen_eq_top G _ hspan
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).mapIso
      (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA) ≪≫
    schemeStructurePerfectCommonAffineCechHomologyIso (Proj G) p hp
      (projectiveProjPresheaf_primeCast G p hR) U V hU hV hcU hcV q

end SerrePositivity.AlgebraicGeometry

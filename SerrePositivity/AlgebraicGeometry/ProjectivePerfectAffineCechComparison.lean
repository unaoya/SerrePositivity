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

/-- 固定した Frobenius 係数の複体の Čech 版の H の対象を共有する。 -/
def projectivePerfectFixedCechH (q : ℕ) : ModuleCat.{u} ℤ :=
  (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).homology q

/-- 標準開における実際の構造層の Čech 版の H の対象を共有する。 -/
def projectivePerfectNativeCechH (q : ℕ) : ModuleCat.{u} ℤ :=
  (fullCechComplex (openCoverCechDiagram
    (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
    (projectiveProjCechOpen (ι := ι) G))).homology q

/-- 任意の有限被覆での、同じ係数の Čech 版の H の対象を共有する。 -/
def projectivePerfectCoverCechH {κ : Type} [LinearOrder κ] [Fintype κ]
    (V : κ → (Proj G).Opens) (q : ℕ) : ModuleCat.{u} ℤ :=
  (fullCechComplex (openCoverCechDiagram
    (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
    V)).homology q

/-- Proj の絶対対角はアフィン。同じ被覆比較の型クラス証明を共有する。 -/
theorem projectivePerfectAffineDiagonal :
    IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from (Proj G))) := inferInstance

attribute [local instance] projectivePerfectAffineDiagonal

/-- 標準開被覆の各開集合はアフィン。被覆比較の証明を分割した補題。 -/
theorem projectivePerfectAffineCechOpen_isAffine (i : ι) :
    IsAffineOpen (projectiveProjCechOpen (ι := ι) G i) :=
  Proj.isAffineOpen_basicOpen G _ (projectivePolynomialVariableImage_mem G i) Nat.zero_lt_one

/-- 変数が irrelevant ideal を生成するなら、同じ標準開は Proj を覆う。 -/
theorem projectivePerfectAffineCechOpen_iSup
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i)))) :
    (⨆ i, projectiveProjCechOpen (ι := ι) G i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top G _ hspan

/-- 固定した標準開の複体比較を Čech H に適用する Čech 版。
BST13 Lemma 3.9 と Stacks 30.2.6 の比較の分割。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectivePerfectNativeCechHomologyIso (q : ℕ) :
    projectivePerfectFixedCechH (ι := ι) G p hp hR hA q ≅
      projectivePerfectNativeCechH (ι := ι) G p hp hR q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).mapIso
    (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA)

/-- 同じ標準開から任意の有限アフィン被覆への既存の共通細分比較の Čech 版。
BST13 Lemma 3.9 と Stacks 30.2.6 の比較の分割。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectivePerfectCommonAffineCechHomologyIso
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
    {κ : Type} [LinearOrder κ] [Fintype κ]
    (V : κ → (Proj G).Opens) (hV : ∀ j, IsAffineOpen (X := Proj G) (V j))
    (hcV : (⨆ j, V j) = ⊤) (q : ℕ) :
    projectivePerfectNativeCechH (ι := ι) G p hp hR q ≅
      projectivePerfectCoverCechH G p hp hR V q :=
  schemeStructurePerfectCommonAffineCechHomologyIso (Proj G) p hp
    (projectiveProjPresheaf_primeCast G p hR) (projectiveProjCechOpen (ι := ι) G) V
    (projectivePerfectAffineCechOpen_isAffine G) hV
    (projectivePerfectAffineCechOpen_iSup G hspan) hcV q

/-- F8 の固定した複体の Čech H と、任意の有限アフィン被覆の実際の Frobenius 係数での比較。
BST13 Lemma 3.9 と Stacks 30.2.6 の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectivePerfectAffineCechHomologyIso
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
    {κ : Type} [LinearOrder κ] [Fintype κ]
    (V : κ → (Proj G).Opens) (hV : ∀ j, IsAffineOpen (X := Proj G) (V j))
    (hcV : (⨆ j, V j) = ⊤) (q : ℕ) :
    (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).homology q ≅
      (fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
        V)).homology q :=
  show projectivePerfectFixedCechH (ι := ι) G p hp hR hA q ≅
      projectivePerfectCoverCechH G p hp hR V q from
    Iso.trans (C := ModuleCat.{u} ℤ)
      (X := projectivePerfectFixedCechH (ι := ι) G p hp hR hA q)
      (Y := projectivePerfectNativeCechH (ι := ι) G p hp hR q)
      (Z := projectivePerfectCoverCechH G p hp hR V q)
      (projectivePerfectNativeCechHomologyIso (ι := ι) G p hp hR hA q)
      (projectivePerfectCommonAffineCechHomologyIso G p hp hR hspan V hV hcV q)

end SerrePositivity.AlgebraicGeometry

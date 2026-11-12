module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveClosedCech
public import SerrePositivity.AlgebraicGeometry.ReesCechImageBounds
public import Mathlib.Algebra.Homology.HomologySequence

/-!
概要：実際の閉厚化の Čech 長完全列から、閉厚化への写像の核を評価する。
方針：短完全な Čech 複体の長完全列を使い、Rees で評価した像と核を同定する。
規約：すべて全タプル Čech コホモロジーであり、導来関手との比較は使わない。
使われ方：射影版の形式関数、BST13 Lemma 3.9 の正次数の議論への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 実際の閉厚化 M/IⁿM の全タプル Čech コホモロジーの対象。 -/
abbrev reesAdicProjectiveClosedCechHomology (n : ℕ) (d : ℤ) (q : ℕ) : ModuleCat.{u} R :=
  (reesAdicProjectiveClosedCechShortComplex (ι := ι) I G n d).X₃.homology q

/-- 実際の閉厚化への射影が誘導する Čech コホモロジーの写像。 -/
def reesAdicProjectiveClosedCechProjection (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveCechTarget (ι := ι) G d q ⟶
      reesAdicProjectiveClosedCechHomology (ι := ι) I G n d q :=
  HomologicalComplex.homologyMap
    (reesAdicProjectiveClosedCechShortComplex (ι := ι) I G n d).g q

/-- 実際の閉厚化の Čech 長完全列の連結写像。
原典 Stacks 30.20.4 の Hⁱ の長完全列の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveClosedCechConnecting (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I G n d q ⟶
      reesAdicProjectiveCechStage (ι := ι) I G n d (q + 1) :=
  (reesAdicProjectiveClosedCechShortComplex_shortExact (ι := ι) I G n d).δ q (q + 1) rfl

/-- 元の加群の Čech コホモロジーにおける、閉厚化の長完全列の完全性。
原典 Stacks 30.20.4 の Hⁱ の長完全列に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCech_exact_middle (n : ℕ) (d : ℤ) (q : ℕ) :
    Function.Exact (reesAdicProjectiveCechToModule (ι := ι) I G n d q).hom
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((reesAdicProjectiveClosedCechShortComplex_shortExact (ι := ι) I G n d).homology_exact₂ q)

/-- 閉厚化の Čech コホモロジーにおける、長完全列の完全性。
原典 Stacks 30.20.4 の Hⁱ の長完全列に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCech_exact_projection_connecting
    (n : ℕ) (d : ℤ) (q : ℕ) :
    Function.Exact (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom
      (reesAdicProjectiveClosedCechConnecting (ι := ι) I G n d q).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((reesAdicProjectiveClosedCechShortComplex_shortExact (ι := ι) I G n d).homology_exact₃
      q (q + 1) rfl)

/-- 次の次数の Čech コホモロジーにおける、長完全列の完全性。
原典 Stacks 30.20.4 の Hⁱ の長完全列に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCech_exact_connecting_inclusion
    (n : ℕ) (d : ℤ) (q : ℕ) :
    Function.Exact (reesAdicProjectiveClosedCechConnecting (ι := ι) I G n d q).hom
      (reesAdicProjectiveCechToModule (ι := ι) I G n d (q + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((reesAdicProjectiveClosedCechShortComplex_shortExact (ι := ι) I G n d).homology_exact₁
      q (q + 1) rfl)

/-- 実際の閉厚化への Čech 写像の核は、IⁿM の Čech 包含の像に等しい。
原典 Stacks 30.20.4(1) の Hⁱ の核に対応する Čech 版の同定。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechProjection_ker_eq_image (n : ℕ) (d : ℤ) (q : ℕ) :
    LinearMap.ker (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom =
      reesAdicProjectiveCechImage (ι := ι) I G n d q :=
  LinearMap.exact_iff.mp (reesAdicProjectiveClosedCech_exact_middle (ι := ι) I G n d q)

/-- 実際の閉厚化への Čech 写像の核の一様な I 進評価。
原典 Stacks 30.20.4(1) の Hⁱ の核の評価の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechProjection_kernel_bound [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    ∃ c : ℕ, ∀ n, c ≤ n →
      LinearMap.ker (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom ≤
        I ^ (n - c) • (⊤ : Submodule R (reesAdicProjectiveCechTarget (ι := ι) G d q)) := by
  obtain ⟨c, hc⟩ := reesAdicProjectiveCechImage_bound (ι := ι) I G d q
  refine ⟨c, ?_⟩
  intro n hn
  rw [reesAdicProjectiveClosedCechProjection_ker_eq_image]
  exact hc n hn

end SerrePositivity.AlgebraicGeometry

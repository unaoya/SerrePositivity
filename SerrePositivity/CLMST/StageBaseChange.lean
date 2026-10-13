module

public import SerrePositivity.CLMST.StageAlgebra
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 根の添加と基底変更の両立

`A_n⊗_A D` と、D 上で `t_i` の像の根を添加した段を D 代数として同定する。
商環の根の生成元を両方向に送り、関係式と逆性を直接確認する。
素数性・Noether 性・局所性を必要としない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 基底変更した段における、左因子から来る根の座標。 -/
abbrev stageRoot (n : ℕ) (i : Fin h) : StageAlgebra A D t p n :=
  algebraMap (TowerStage A t p n) (StageAlgebra A D t p n)
    (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i))

/-- A 上の根の段から、D 上の対応する根の段への係数変更写像。 -/
def stageMap (n : ℕ) :
    TowerStage A t p n →ₐ[A] TowerStage D (algebraMap A D ∘ t) p n :=
  Ideal.Quotient.liftₐ (towerRel A t p n)
    (MvPolynomial.aeval fun i ↦
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i))
    (relIdeal_apply_eq_zero t (p ^ n) _ (by
      intro i
      rw [MvPolynomial.aeval_X, mk_X_pow]
      exact (IsScalarTower.algebraMap_apply A D
        (TowerStage D (algebraMap A D ∘ t) p n) (t i)).symm))

/-- 係数変更写像は多項式代表元を、対応する D 上の根で評価する。 -/
@[simp] theorem stageMap_mk (n : ℕ) (f : MvPolynomial (Fin h) A) :
    stageMap A D t p n (Ideal.Quotient.mk (towerRel A t p n) f) =
      MvPolynomial.aeval (R := A) (fun i ↦
        Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i)) f := rfl

/-- 係数変更写像は A 上の根の座標を D 上の根の座標へ送る。 -/
@[simp] theorem stageMap_mk_X (n : ℕ) (i : Fin h) :
    stageMap A D t p n (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i) := by
  rw [stageMap_mk, MvPolynomial.aeval_X]

/-- テンソル積の左因子の根を D 上の根へ送る、基底変更の標準写像。 -/
def stageBaseChangeTo (n : ℕ) :
    StageAlgebra A D t p n →ₐ[D] TowerStage D (algebraMap A D ∘ t) p n := by
  letI : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.lift
    (Algebra.ofId D (TowerStage D (algebraMap A D ∘ t) p n))
    (stageMap A D t p n) (fun _ _ ↦ Commute.all _ _)).comp
      (Algebra.TensorProduct.commRight A D (TowerStage A t p n)).symm.toAlgHom

/-- 基底変更の標準写像は、単純テンソルを二つの因子の像の積へ送る。 -/
@[simp] theorem stageBaseChangeTo_tmul (n : ℕ) (x : TowerStage A t p n) (d : D) :
    stageBaseChangeTo A D t p n (x ⊗ₜ[A] d) =
      algebraMap D (TowerStage D (algebraMap A D ∘ t) p n) d * stageMap A D t p n x := rfl

/-- 標準写像は左側の根の座標を、D 上の対応する根へ送る。 -/
@[simp] theorem stageBaseChangeTo_stageRoot (n : ℕ) (i : Fin h) :
    stageBaseChangeTo A D t p n (stageRoot A D t p n i) =
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i) := by
  change stageBaseChangeTo A D t p n
    (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i) ⊗ₜ[A] 1) = _
  simp

/-- D 上の根をテンソル積の左因子の根へ送る、基底変更写像の逆。 -/
def stageBaseChangeInv (n : ℕ) :
    TowerStage D (algebraMap A D ∘ t) p n →ₐ[D] StageAlgebra A D t p n :=
  Ideal.Quotient.liftₐ (towerRel D (algebraMap A D ∘ t) p n)
    (MvPolynomial.aeval (stageRoot A D t p n))
    (relIdeal_apply_eq_zero (algebraMap A D ∘ t) (p ^ n) _ (by
      intro i
      rw [MvPolynomial.aeval_X]
      change (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n)
        (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i))) ^ (p ^ n) = _
      rw [← map_pow, mk_X_pow]
      rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p n) (StageAlgebra A D t p n)]
      exact IsScalarTower.algebraMap_apply A D (StageAlgebra A D t p n) (t i)))

/-- 逆写像は D 上の根の座標を、基底変更した段の左側の根へ送る。 -/
@[simp] theorem stageBaseChangeInv_mk_X (n : ℕ) (i : Fin h) :
    stageBaseChangeInv A D t p n
      (Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i)) =
        stageRoot A D t p n i := by
  change MvPolynomial.aeval (stageRoot A D t p n) (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

/-- 係数変更の後に逆写像を適用すると、テンソル積の左因子の標準像となる。 -/
theorem stageBaseChangeInv_stageMap (n : ℕ) (x : TowerStage A t p n) :
    stageBaseChangeInv A D t p n (stageMap A D t p n x) =
      algebraMap (TowerStage A t p n) (StageAlgebra A D t p n) x := by
  have he : ((stageBaseChangeInv A D t p n).restrictScalars A).comp (stageMap A D t p n) =
      IsScalarTower.toAlgHom A (TowerStage A t p n) (StageAlgebra A D t p n) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk,
      stageMap_mk_X, stageBaseChangeInv_mk_X]
    rfl
  exact AlgHom.congr_fun he x

/-- 根の添加は基底変更と両立する。
`A_n⊗_A D` は、D 上で `t_i` の像の根を添加した段と D 代数として同型。 -/
def stageBaseChangeEquiv (n : ℕ) :
    StageAlgebra A D t p n ≃ₐ[D] TowerStage D (algebraMap A D ∘ t) p n := by
  refine AlgEquiv.ofAlgHom (stageBaseChangeTo A D t p n) (stageBaseChangeInv A D t p n) ?_ ?_
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
      stageBaseChangeInv_mk_X, stageBaseChangeTo_stageRoot]
  · apply AlgHom.ext
    intro x
    change TowerStage A t p n ⊗[A] D at x
    induction x using TensorProduct.inductionOn with
    | tmul x d =>
      simp only [AlgHom.comp_apply, AlgHom.id_apply, stageBaseChangeTo_tmul, map_mul,
        AlgHom.commutes, stageBaseChangeInv_stageMap]
      change (1 ⊗ₜ[A] d) * (x ⊗ₜ[A] 1) = x ⊗ₜ[A] d
      simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- 基底変更同型は D の標準的な係数を保つ。 -/
@[simp] theorem stageBaseChangeEquiv_algebraMap_D (n : ℕ) (d : D) :
    stageBaseChangeEquiv A D t p n (algebraMap D (StageAlgebra A D t p n) d) =
      algebraMap D (TowerStage D (algebraMap A D ∘ t) p n) d :=
  (stageBaseChangeEquiv A D t p n).commutes d

/-- 基底変更同型は、根の座標を対応する D 上の根へ送る。 -/
@[simp] theorem stageBaseChangeEquiv_stageRoot (n : ℕ) (i : Fin h) :
    stageBaseChangeEquiv A D t p n (stageRoot A D t p n i) =
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i) :=
  stageBaseChangeTo_stageRoot A D t p n i

end SerrePositivity.CLMST

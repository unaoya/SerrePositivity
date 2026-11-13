module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechIntComparison
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechCompletion
public import SerrePositivity.AlgebraicGeometry.ProjectiveFormalFunctionsBounds

/-!
概要：2e の核の評価と像の安定化を、整数係数の同じ Čech 写像へ移す。
方針：射影・遷移との自然な加法群同型で単射性と像の持ち上げを移送する。
規約：Stacks 30.20.4 と BST13 Lemma 3.9 の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
使われ方：F6 では F5 が零化の仮定を供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable [LinearOrder ι] [Fintype ι]
variable (I : Ideal R) (G : ℕ → Submodule R A) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedMonoid G]
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]

/-- 元の Čech H が中心の冪で零化されれば、十分厚い閉厚化への射影は単射。 -/
theorem reesClosedCechIntProjection_eventually_injective (q : ℕ)
    (hkill : ∃ k : ℕ, I ^ k •
      (⊤ : Submodule R (reesAdicProjectiveCechTarget (ι := ι) G 0 q)) = ⊥) :
    ∃ N : ℕ, ∀ n, N ≤ n → Function.Injective (reesClosedCechIntProjection (ι := ι) I G n q) := by
  obtain ⟨k, hk⟩ := hkill
  obtain ⟨c, hc⟩ := reesAdicProjectiveClosedCechProjection_kernel_bound (ι := ι) I G 0 q
  have hinj := formalFunctions_eventually_injective_of_kernel_bound I
    (fun n ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 q).hom) c k hc hk
  refine ⟨c + k, ?_⟩
  intro n hn x y hxy
  apply (projectiveCechIntToModuleEquiv (ι := ι) G q).injective
  apply hinj n hn
  rw [← reesClosedCechIntToModuleEquiv_projection,
    ← reesClosedCechIntToModuleEquiv_projection, hxy]

/-- 十分厚い段からの遷移の像は、元の Čech H の実際の射影から持ち上がる。 -/
theorem reesClosedCechIntTransition_eventually_lifts (q : ℕ) :
    ∃ c : ℕ, ∀ n l (hl : n + c ≤ l)
      (x : ReesClosedCechIntHomology (ι := ι) I G l q),
      ∃ y : ProjectiveCechIntHomology (ι := ι) G q,
        reesClosedCechIntProjection (ι := ι) I G n q y =
        reesClosedCechIntTransition (ι := ι) I G l n
          ((Nat.le_add_right n c).trans hl) q x := by
  obtain ⟨c, hc⟩ := reesAdicProjectiveClosedCechTransition_range_stabilizes (ι := ι) I G 0 q
  refine ⟨c, ?_⟩
  intro n l hl x
  have hx : (reesAdicProjectiveClosedCechTransition (ι := ι) I G l n
      ((Nat.le_add_right n c).trans hl) 0 q).hom
      (reesClosedCechIntToModuleEquiv (ι := ι) I G l q x) ∈
      LinearMap.range (reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 q).hom := by
    rw [← hc n l hl]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := hx
  refine ⟨(projectiveCechIntToModuleEquiv (ι := ι) G q).symm y, ?_⟩
  apply (reesClosedCechIntToModuleEquiv (ι := ι) I G n q).injective
  rw [reesClosedCechIntToModuleEquiv_projection, reesClosedCechIntToModuleEquiv_transition,
    AddEquiv.apply_symm_apply]
  exact hy

end SerrePositivity.AlgebraicGeometry

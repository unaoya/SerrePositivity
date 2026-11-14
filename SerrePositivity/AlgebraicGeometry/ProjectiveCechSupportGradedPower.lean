module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSupportPower
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechTransition

/-!
概要：F5 の実際の Proj の零化を、標準開の次数付き加群表示へ移す。
方針：構造層の Čech 複体との既存の自然な比較で、各スカラーの作用を照合する。
規約：BST13 Lemma 3.9 の正次数の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
使われ方：F6 の核の評価に要る中心の冪による零化を、幾何学の条件から供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 中心外で同型な射影スキームの正次数 Čech H の次数表示も、中心のある冪で零化される。 -/
theorem projectiveCechSupport_graded_power_annihilates
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
    (I : Ideal R)
    [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
      affineCenterComplement I)] (q : ℕ) (hq : 0 < q) :
    ∃ k : ℕ, I ^ k •
      (⊤ : Submodule R (reesAdicProjectiveCechTarget (ι := ι) G 0 q)) = ⊥ := by
  obtain ⟨k, hk⟩ := projectiveCechSupport_power_annihilates (ι := ι) G hspan I q hq
  let e := ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    (projectiveProjNativeNatCechComplexIso (ι := ι) G)).toLinearEquiv
  refine ⟨k, le_antisymm ?_ bot_le⟩
  apply Submodule.smul_le.mpr
  intro r hr x _
  change r • x = 0
  apply e.injective
  rw [map_smul, map_zero]
  exact Module.mem_annihilator.mp (hk hr) (e x)

end SerrePositivity.AlgebraicGeometry

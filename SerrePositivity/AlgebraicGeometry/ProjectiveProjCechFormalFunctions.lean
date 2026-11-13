module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjAdicCechHomology
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
概要：実際の Proj とその閉厚化の構造層について、Čech 形式関数を与える。
方針：Rees の形式関数を、射影と I 進遷移に自然な同型で移す。
規約：導来関手の H との比較は追加せず、実際の引き戻しによる互換族を使う。
使われ方：BST13 Lemma 3.9 の射影版の正次数と次数零の評価。
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
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S]

/-- 実際の Proj と閉厚化の構造層に対する Čech 版の形式関数の同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjCechFormalFunctions (q : ℕ) :
    AdicCompletion I (projectiveProjSourceCechHomology (ι := ι) G q) ≃ₗ[R]
      projectiveProjAdicCechFamilies (ι := ι) I G q :=
  ((AdicCompletion.congr I
    (projectiveProjSourceCechHomologyIso (ι := ι) G q).toLinearEquiv.symm).restrictScalars R).trans
      ((reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G 0 q).trans
        (projectiveProjAdicCechFamiliesEquiv (ι := ι) I G q))

/-- Čech 形式関数の同型は、元の切断のコホモロジーを実際の閉厚化へ制限する。
原典 Stacks 30.20.5 の Hⁱ に対する標準写像の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveProjCechFormalFunctions_of_apply (q : ℕ)
    (m : projectiveProjSourceCechHomology (ι := ι) G q) (n : ℕ) :
    (projectiveProjCechFormalFunctions (ι := ι) I G q (AdicCompletion.of I _ m)).val n =
      (projectiveProjAdicCechHomologyProjection (ι := ι) I G n q).hom m := by
  change (projectiveProjAdicCechHomologyIso (ι := ι) I G n q).hom.hom
    ((reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G 0 q
      (AdicCompletion.map I
        (projectiveProjSourceCechHomologyIso (ι := ι) G q).toLinearEquiv.symm.toLinearMap
        (AdicCompletion.of I _ m))).val n) = _
  rw [AdicCompletion.map_of]
  change (projectiveProjAdicCechHomologyIso (ι := ι) I G n q).hom.hom
    ((reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 q).hom
      ((projectiveProjSourceCechHomologyIso (ι := ι) G q).inv.hom m)) = _
  have hp := congrArg
    (fun f ↦ f.hom ((projectiveProjSourceCechHomologyIso (ι := ι) G q).inv.hom m))
    (projectiveProjAdicCechHomologyIso_projection (ι := ι) I G n q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  have he : (projectiveProjSourceCechHomologyIso (ι := ι) G q).hom.hom
      ((projectiveProjSourceCechHomologyIso (ι := ι) G q).inv.hom m) = m :=
    congrArg (fun f ↦ ModuleCat.Hom.hom f m)
      (projectiveProjSourceCechHomologyIso (ι := ι) G q).inv_hom_id
  exact hp.trans (congrArg
    (projectiveProjAdicCechHomologyProjection (ι := ι) I G n q).hom he)

end SerrePositivity.AlgebraicGeometry

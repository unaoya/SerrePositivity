module

public import Mathlib.RingTheory.Localization.BaseChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizationMapRestriction

/-!
概要：標準開で使う加群の局所化と、右側のテンソル積を比較する。
方針：Mathlib の局所化の普遍性をテンソル積へ移し、分数の代表で計算する。
規約：局所化する環 P とテンソルの基底環 R を分け、平坦性は仮定しない。
使われ方：Proj の標準開の分数表示と、Čech のテンソル底変換を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R P M N Q : Type*} [CommRing R] [CommRing P] [Algebra R P]
variable [AddCommGroup M] [Module R M] [Module P M] [IsScalarTower R P M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup Q] [Module R Q] [Module P Q] [IsScalarTower R P Q]
variable (S : Submonoid P)

/-- 同じ分母を持つ局所化の分数は、分子について加法的である。 -/
theorem projectiveLocalizedModule_mk_add (x y : M) (s : S) :
    LocalizedModule.mk (x + y) s = LocalizedModule.mk x s + LocalizedModule.mk y s := by
  rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]

/-- 加群の実際の局所化と右テンソル積を交換する、P 線形な同型。 -/
def projectiveRightTensorLocalizationEquiv :
    LocalizedModule S (M ⊗[R] N) ≃ₗ[P] (LocalizedModule S M) ⊗[R] N :=
  IsLocalizedModule.iso S (TensorProduct.AlgebraTensorModule.rTensor R N
    (LocalizedModule.mkLinearMap S M))

/-- 局所化と右テンソル積の比較は、分母一の純テンソルを保つ。 -/
theorem projectiveRightTensorLocalizationEquiv_mk_one (m : M) (n : N) :
    projectiveRightTensorLocalizationEquiv (R := R) S
        (LocalizedModule.mk (m ⊗ₜ[R] n) 1) = LocalizedModule.mk m 1 ⊗ₜ[R] n :=
  IsLocalizedModule.iso_mk_one S _ (m ⊗ₜ[R] n)

/-- 局所化と右テンソル積の比較は、純テンソルの分母を保つ。 -/
theorem projectiveRightTensorLocalizationEquiv_mk (m : M) (n : N) (s : S) :
    projectiveRightTensorLocalizationEquiv (R := R) S
        (LocalizedModule.mk (m ⊗ₜ[R] n) s) = LocalizedModule.mk m s ⊗ₜ[R] n := by
  let g := TensorProduct.AlgebraTensorModule.rTensor R N (LocalizedModule.mkLinearMap S M)
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).1
  change s.val • projectiveRightTensorLocalizationEquiv (R := R) S
      (LocalizedModule.mk (m ⊗ₜ[R] n) s) = s.val • (LocalizedModule.mk m s ⊗ₜ[R] n)
  have hcT (x : M ⊗[R] N) :
      s.val • LocalizedModule.mk x s = LocalizedModule.mk x 1 := by
    rw [LocalizedModule.smul'_mk]
    simpa only [Submonoid.smul_def] using LocalizedModule.mk_cancel s x
  have hcM : s.val • LocalizedModule.mk m s = LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    simpa only [Submonoid.smul_def] using LocalizedModule.mk_cancel s m
  calc
    _ = projectiveRightTensorLocalizationEquiv (R := R) S
        (s.val • LocalizedModule.mk (m ⊗ₜ[R] n) s) :=
      ((projectiveRightTensorLocalizationEquiv (R := R) S).map_smul s.val _).symm
    _ = projectiveRightTensorLocalizationEquiv (R := R) S
        (LocalizedModule.mk (m ⊗ₜ[R] n) 1) := congrArg _ (hcT _)
    _ = LocalizedModule.mk m 1 ⊗ₜ[R] n := projectiveRightTensorLocalizationEquiv_mk_one S m n
    _ = _ := congrArg (fun x : LocalizedModule S M ↦ x ⊗ₜ[R] n) hcM.symm

/-- 局所化と右テンソル積の比較は、P 線形な加群写像に自然。 -/
theorem projectiveRightTensorLocalizationEquiv_naturality (f : M →ₗ[P] Q)
    (z : LocalizedModule S (M ⊗[R] N)) :
    projectiveRightTensorLocalizationEquiv (R := R) S
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (M ⊗[R] N))
          (LocalizedModule.mkLinearMap S (Q ⊗[R] N))
          (TensorProduct.AlgebraTensorModule.rTensor R N f) z) =
      TensorProduct.AlgebraTensorModule.rTensor R N
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
          (LocalizedModule.mkLinearMap S Q) f)
        (projectiveRightTensorLocalizationEquiv (R := R) S z) := by
  induction z using LocalizedModule.induction_on with
  | _ x s =>
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      simp only [IsLocalizedModule.map_LocalizedModules,
        TensorProduct.AlgebraTensorModule.rTensor_tmul, projectiveRightTensorLocalizationEquiv_mk]
    | add x y hx hy => simp only [projectiveLocalizedModule_mk_add, map_add, hx, hy]

/-- 局所化と右テンソル積の比較は、標準開を狭める制限にも自然。 -/
theorem projectiveRightTensorLocalizationEquiv_restriction {f g a : P}
    (ha : g = f * a) (z : LocalizedModule (Submonoid.powers f) (M ⊗[R] N)) :
    projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers g)
        (projectiveModuleAwayRestriction (M := M ⊗[R] N) (show f ∣ g from ⟨a, ha⟩) z) =
      TensorProduct.AlgebraTensorModule.rTensor R N
        (projectiveModuleAwayRestriction (M := M) (show f ∣ g from ⟨a, ha⟩))
        (projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers f) z) := by
  induction z using LocalizedModule.induction_on with
  | _ x s =>
    obtain ⟨s, k, rfl⟩ := s
    change projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers g)
        (projectiveModuleAwayRestriction (M := M ⊗[R] N) (show f ∣ g from ⟨a, ha⟩)
          (LocalizedModule.mk x (projDenominator f k))) =
      TensorProduct.AlgebraTensorModule.rTensor R N
        (projectiveModuleAwayRestriction (M := M) (show f ∣ g from ⟨a, ha⟩))
        (projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers f)
          (LocalizedModule.mk x (projDenominator f k)))
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      rw [projectiveModuleAwayRestriction_mk ha]
      change projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers g)
          (LocalizedModule.mk ((a ^ k • m) ⊗ₜ[R] n) (projDenominator g k)) =
        TensorProduct.AlgebraTensorModule.rTensor R N
          (projectiveModuleAwayRestriction (M := M) (show f ∣ g from ⟨a, ha⟩))
          (projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers f)
            (LocalizedModule.mk (m ⊗ₜ[R] n) (projDenominator f k)))
      rw [projectiveRightTensorLocalizationEquiv_mk, projectiveRightTensorLocalizationEquiv_mk,
        TensorProduct.AlgebraTensorModule.rTensor_tmul, projectiveModuleAwayRestriction_mk ha]
    | add x y hx hy => simp only [projectiveLocalizedModule_mk_add, map_add, hx, hy]

end SerrePositivity.AlgebraicGeometry

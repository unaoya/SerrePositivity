module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedTensorLocalization
public import SerrePositivity.AlgebraicGeometry.TensorCoefficientRightModule
public import SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarLocalizationRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedScalarRestriction

/-!
概要：テンソル像の分子族を持つ斉次局所化を、変更後の係数環上で比較する。
方針：固定環でのテンソル比較と局所化環の変更を合成し、純テンソル分数で線形性を示す。
規約：元の局所化環 P に B 代数構造は仮定しない。共通の変更先 Q を使う。
使われ方：R[X] と B[X] の標準開を B 線形に比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R B P Q M : Type*} [CommRing R] [CommRing B] [CommRing P] [CommRing Q]
variable [Algebra R B] [Algebra R P] [Algebra P Q] [Algebra R Q] [Algebra B Q]
variable [IsScalarTower R P Q] [IsScalarTower R B Q]
variable [AddCommGroup M] [Module R M] [Module P M] [IsScalarTower R P M]
local instance projectiveTensorCoeffRightModule {V : Type*}
    [AddCommGroup V] [Module R V] : Module B (V ⊗[R] B) := tensorRightCoefficientModule
local instance projectiveTensorCoeffRightTower {V : Type*}
    [AddCommGroup V] [Module R V] : IsScalarTower R B (V ⊗[R] B) :=
  tensorRightCoefficient_scalarTower
variable [Module Q (M ⊗[R] B)] [IsScalarTower P Q (M ⊗[R] B)]
variable [IsScalarTower R Q (M ⊗[R] B)] [IsScalarTower B Q (M ⊗[R] B)]
variable (f : P) (g : Q) (hg : algebraMap P Q f = g) (V : ℕ → Submodule R M)

/-- 分子族のテンソル像を、変更後の基底環 B 上の部分加群として扱う。 -/
def projectiveTensorCoefficientNumerator (n : ℕ) : Submodule B (M ⊗[R] B) :=
  LinearMap.range (tensorRightCoefficientMap (B := B) (V n).subtype)

/-- B 上の分子のテンソル像を R に制限すると、元の R 上のテンソル像になる。 -/
theorem projectiveTensorCoefficientNumerator_restrict (n : ℕ) :
    (projectiveTensorCoefficientNumerator (B := B) V n).restrictScalars R =
      projectiveTensorNumerator (N := B) V n := rfl

/-- 局所化する環を変えた、指定分子族のテンソル比較。まず R 線形に構成する。 -/
def projectiveGradedTensorCoefficientEquiv [Module.Flat R B] :
    (projectiveGradedAway f V) ⊗[R] B ≃ₗ[R]
      projectiveGradedAway g (projectiveTensorCoefficientNumerator (B := B) V) :=
  (projectiveGradedTensorLocalizationEquiv (N := B) f V).trans
    ((projectiveModuleScalarGradedAwayLinearEquivOfEq (R := R) f g hg
      (projectiveTensorNumerator (N := B) V)).trans
      ((projectiveGradedAwayScalarRestrictionLinearEquiv (R := R) g
        (projectiveTensorCoefficientNumerator (B := B) V)).trans
        (projectiveModuleScalarRestrictionLinearEquiv (R := R) (B := B)).symm))

/-- 係数環の変更を含めた比較も、純テンソル分数の分子と分母の冪を保つ。 -/
theorem projectiveGradedTensorCoefficientEquiv_fraction [Module.Flat R B]
    (n : ℕ) (m : V n) (b : B) (u : projectiveGradedAway f V)
    (hu : u.val = projectiveGradedFraction f V n m) :
    (projectiveGradedTensorCoefficientEquiv f g hg V (u ⊗ₜ[R] b)).val =
      LocalizedModule.mk (m.val ⊗ₜ[R] b) (projDenominator g n) := by
  let z := projectiveGradedTensorLocalizationEquiv (N := B) f V (u ⊗ₜ[R] b)
  have hz : projectiveGradedFraction f (projectiveTensorNumerator (N := B) V) n
      ⟨m.val ⊗ₜ[R] b, ⟨m ⊗ₜ[R] b, rfl⟩⟩ = z.val := by
    rw [projectiveGradedFraction_apply]
    exact (projectiveGradedTensorLocalizationMap_fraction f V n m b u hu).symm
  change (projectiveModuleScalarGradedAwayLinearEquivOfEq (R := R) f g hg
    (projectiveTensorNumerator (N := B) V) z).val = _
  rw [projectiveModuleScalarGradedAwayLinearEquivOfEq_fraction _ _ _ _ n _ z hz,
    projectiveGradedFraction_apply]

/-- 分子族が分母倍で次へ移るなら、係数変更を含む比較は B の作用と可換。 -/
theorem projectiveGradedTensorCoefficientEquiv_smul [Module.Flat R B]
    (hstep : ∀ n (m : V n), f • m.val ∈ V (n + 1))
    (c : B) (z : (projectiveGradedAway f V) ⊗[R] B) :
    projectiveGradedTensorCoefficientEquiv f g hg V (c • z) =
      c • projectiveGradedTensorCoefficientEquiv f g hg V z := by
  induction z using TensorProduct.inductionOn with
  | tmul u b =>
    obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f V hstep u.val).mp u.property
    apply Subtype.ext
    rw [tensorRightCoefficient_smul_tmul]
    change (projectiveGradedTensorCoefficientEquiv f g hg V (u ⊗ₜ[R] (c * b))).val =
      c • (projectiveGradedTensorCoefficientEquiv f g hg V (u ⊗ₜ[R] b)).val
    rw [projectiveGradedTensorCoefficientEquiv_fraction f g hg V n m _ u hm.symm,
      projectiveGradedTensorCoefficientEquiv_fraction f g hg V n m _ u hm.symm,
      LocalizedModule.smul'_mk, tensorRightCoefficient_smul_tmul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- flat な基底変更と斉次局所化の比較を、B 線形な同型にする。 -/
def projectiveGradedTensorCoefficientLinearEquiv [Module.Flat R B]
    (hstep : ∀ n (m : V n), f • m.val ∈ V (n + 1)) :
    (projectiveGradedAway f V) ⊗[R] B ≃ₗ[B]
      projectiveGradedAway g (projectiveTensorCoefficientNumerator (B := B) V) where
  toFun := projectiveGradedTensorCoefficientEquiv f g hg V
  invFun := (projectiveGradedTensorCoefficientEquiv f g hg V).symm
  left_inv := (projectiveGradedTensorCoefficientEquiv f g hg V).left_inv
  right_inv := (projectiveGradedTensorCoefficientEquiv f g hg V).right_inv
  map_add' := (projectiveGradedTensorCoefficientEquiv f g hg V).map_add
  map_smul' c z := projectiveGradedTensorCoefficientEquiv_smul f g hg V hstep c z

end SerrePositivity.AlgebraicGeometry

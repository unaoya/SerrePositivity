module

public import SerrePositivity.AlgebraicGeometry.EtaleFiberInductionGluing
public import SerrePositivity.AlgebraicGeometry.FlatCenterDimensionZero
public import SerrePositivity.AlgebraicGeometry.UniformFiberSupportBound
public import Mathlib.Data.ENat.Monoid

/-!
概要：Noether アフィン基底上の有限型代数の有限加群を、許容ブローアップで平坦化する。
方針：零化イデアルの商でファイバー台を切り出し、その次元の一様な上限で帰納する。
規約：境界は正則元による主開とする。
使われ方：Stacks 0815 のアフィン平坦化から、有限型射の狭義変換の平坦性へ進む。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false in
/--
概要：ファイバー台の次元に一を足した値の上限について、平坦化の帰納が一段進む。
方針：零化イデアルの商のファイバー次元を取り、étale 局所で得た中心を降下する。
規約：加群の基礎環上の作用は商を取る前後で同じ。
使われ方：すべての有限の次元上限に対して平坦化中心の存在を導く。
-/
theorem HasAffineFlatPureCentersBelow.succ {n : ℕ}
    (ih : HasAffineFlatPureCentersBelow.{u} n) : HasAffineFlatPureCentersBelow.{u} (n + 1) := by
  intro R _ B M _ _ _ _ _ _ _ _ a ha hflat hdim
  let E := CommRingCat.of (B ⧸ Module.annihilator B M)
  let : Module E M := Module.quotientAnnihilator (R := B) (M := M)
  let : IsScalarTower B E M := (Module.isTorsionBySet_annihilator B M).isScalarTower
  let : IsScalarTower R E M := IsScalarTower.to₁₃₄ R B E M
  let : Module.Finite E M := finite_quotientAnnihilator B M
  let : Algebra.FiniteType R E :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective
  have hE (p : PrimeSpectrum R) : ringKrullDim (p.asIdeal.Fiber E) ≤ n := by
    have hp := hdim p
    dsimp only at hp
    rw [supportDim_baseChange_eq_ringKrullDim_quotientAnnihilator, Nat.cast_add, Nat.cast_one] at hp
    exact ENat.WithBot.add_le_add_one_right_iff.mp hp
  exact exists_affine_flatPure_center_of_fiber_dimension_induction R E (M := M) a ha n hE ih

/--
概要：有限型代数上有限な加群で、正則な境界の外で基底上平坦なら、許容なアフィン中心で純変換を平坦化できる。
方針：全ファイバーの台の次元の一様な上限を取り、その自然数で帰納する。
規約：加群の基礎環上の有限性は不要。
使われ方：有限型アフィン開の構造層を平坦化する。
-/
theorem exists_affine_flatPure_center_of_finiteType
    {R : CommRingCat.{u}} {B M : Type u} [IsNoetherianRing R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [Module.Finite B M]
    (a : R) (ha : IsRegular a)
    (hflat : Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] M)) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) a M := by
  obtain ⟨n, hn⟩ := exists_uniform_supportDim_fiber_bound (R := R) (B := B) (M := M)
  have hrec (k : ℕ) : HasAffineFlatPureCentersBelow.{u} k := by
    induction k with
    | zero => exact hasAffineFlatPureCentersBelow_zero
    | succ k ih => exact ih.succ
  exact hrec n R B M a ha hflat hn

end SerrePositivity.AlgebraicGeometry

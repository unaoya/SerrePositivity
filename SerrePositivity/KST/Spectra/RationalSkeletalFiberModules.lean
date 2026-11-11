module

public import SerrePositivity.KST.Spectra.SkeletalFiberAbelian
public import SerrePositivity.KST.Spectra.RationalHomotopyModules
public import SerrePositivity.KST.Spectra.AdditiveFunctionEquiv
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
概要：有理化係数の骨格の fiber の群と微分への有理線形構造。
方針：telescope の群の計算で得た有理作用をセルの係数表示で移す。
規約：実際の有理化スペクトルを係数に使い、群の有理性を追加仮定しない。
使われ方：BF 1978 §2、Goerss–Jardine VIII §1。有理 E_1 の線形な微分。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：有理化の段を係数とするセルの関数群に有理作用を与える。
方針：各係数の有理作用を関数へ広げ、加法のタグの比較で移す。
規約：係数の実際の次数は n+r+2。
使われ方：BF 1978 §2、Goerss–Jardine VIII §1。骨格の有理係数群。 -/
instance rationalCoefficientModule (K : SSet.{u}) (X : OmegaSpectrum.{u}) (k n r : ℕ) :
    Module ℚ (Additive (coefficientGroup K ((OmegaSpectrum.rationalization X).level k).space
      n r)) := by
  let Y := ((OmegaSpectrum.rationalization X).level k).space
  let : Module ℚ (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + r) Y.basepoint)) := by
    rw [show n + 1 + r = (n + r) + 1 by omega]
    exact OmegaSpectrum.rationalizationLevelModule X k (n + r)
  exact (additiveFunctionEquiv (K.nonDegenerate (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + r) Y.basepoint)).module ℚ

/-- 概要：有理化の段への骨格写像空間の fiber の群は有理加群。
方針：係数の関数群の有理作用を実際の fiber の群同型で移す。
規約：fiber の一次群も含む全正次数。
使われ方：BF 1978 §2、Goerss–Jardine VIII §1。有理な塔の群の供給。 -/
instance rationalStageFiberModule (K : SSet.{u}) (X : OmegaSpectrum.{u}) (k n r : ℕ) :
    Module ℚ (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (UnbasedPointedMapping.stageFiber K
        ((OmegaSpectrum.rationalization X).level k).space n).right r
      (UnbasedPointedMapping.stageFiber K
        ((OmegaSpectrum.rationalization X).level k).space n).basepoint)) :=
  (MulEquiv.toAdditive
    (stageFiberCoefficientEquiv K ((OmegaSpectrum.rationalization X).level k).space n r)).module ℚ

/-- 概要：有理化係数のセルの微分は有理線形写像。
方針：加法群の射は有理加群の間では自動的に有理線形であることを使う。
規約：線形写像の基礎写像は実際の幾何的微分を移したもの。
使われ方：Goerss–Jardine VIII §1。有理 E_1 の複体の微分。 -/
def rationalCoefficientDifferential (K : SSet.{u}) (X : OmegaSpectrum.{u}) (k n r : ℕ) :
    Additive (coefficientGroup K ((OmegaSpectrum.rationalization X).level k).space n (r + 1)) →ₗ[ℚ]
      Additive (coefficientGroup K ((OmegaSpectrum.rationalization X).level k).space (n + 1) r) :=
  (coefficientDifferential K ((OmegaSpectrum.rationalization X).level k).space n r).toAdditive
    |>.toRatLinearMap

set_option maxRecDepth 4096 in
/-- 概要：有理線形なセルの微分の二乗は零。
方針：実際の fiber の微分から移した零合成を加法記法にする。
規約：収束と通常の交代微分の式との比較は含まない。
使われ方：Goerss–Jardine VIII §1。有理な複体条件。 -/
@[simp]
theorem rationalCoefficientDifferential_comp (K : SSet.{u}) (X : OmegaSpectrum.{u}) (k n r : ℕ)
    (a : Additive (coefficientGroup K ((OmegaSpectrum.rationalization X).level k).space
      n (r + 2))) :
    rationalCoefficientDifferential K X k (n + 1) r
      (rationalCoefficientDifferential K X k n (r + 1) a) = 0 := by
  simpa only [rationalCoefficientDifferential, AddMonoidHom.coe_toRatLinearMap,
    MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul, ofMul_one] using
    congrArg Additive.ofMul
      (coefficientDifferential_comp K ((OmegaSpectrum.rationalization X).level k).space n r a.toMul)

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment

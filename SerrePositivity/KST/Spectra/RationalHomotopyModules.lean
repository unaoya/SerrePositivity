module

public import SerrePositivity.KST.Spectra.RationalSpectrum
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Field.ULift

/-!
概要：有理化スペクトルの安定ホモトピー群と各段の高次群への有理係数構造。
方針：telescope のテンソル積同型と任意段表示から加群構造を移す。
規約：係数構造は実際の有理化対象に与える。任意の群を有理化したとは仮定しない。
使われ方：BF 1978 §2、HA §1.4.2。有理群 cochain の具体的な係数の供給。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：有理化の安定群を有理数が左因子のテンソル積で表示する。
方針：telescope の群の計算とテンソル積の対称同型を合成する。
規約：この段階の同型は加法群の同型。
使われ方：BF 1978 §2、HA §1.4.2。有理係数作用の移送。 -/
def rationalizationAddEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    Additive (homotopyGroup (rationalization X) j) ≃+
      ℚ ⊗[ℤ] Additive (homotopyGroup X j) :=
  (rationalizationTensorEquiv X j).toAddEquiv.trans
    (TensorProduct.comm ℤ _ _).toAddEquiv

/-- 概要：実際の有理化スペクトルの全整数次数の群は ℚ 加群。
方針：有理数を左因子とするテンソル積の作用を群同型で移す。
規約：乗法表示の安定群を Additive へ送って作用を与える。
使われ方：BF 1978 §2、HA §1.4.2。有理 Shapiro の係数。 -/
instance rationalizationHomotopyModule (X : OmegaSpectrum.{u}) (j : ℤ) :
    Module ℚ (Additive (homotopyGroup (rationalization X) j)) :=
  (rationalizationAddEquiv X j).module ℚ

/-- 概要：有理化のテンソル積表示は移した有理係数構造について線形。
方針：加法同型による加群構造の移送の標準線形同型を使う。
規約：有理数を左因子とする表示を用いる。
使われ方：BF 1978 §2、HA §1.4.2。有理係数構造と群の計算の整合性。 -/
def rationalizationLinearEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    Additive (homotopyGroup (rationalization X) j) ≃ₗ[ℚ]
      ℚ ⊗[ℤ] Additive (homotopyGroup X j) where
  __ := rationalizationAddEquiv X j
  map_smul' _ _ := (rationalizationAddEquiv X j).apply_symm_apply _

/-- 概要：各段の二以上の次数の群を安定群で表示する。
方針：安定次数 q+2-k の任意段表示を反転し、計算次数を整える。
規約：q は実際のホモトピー次数 q+2、k はスペクトルの段。
使われ方：BF 1978 §2、HA §1.4.2。段ごとの群へ係数構造を移す。 -/
def positiveLevelStableEquiv (X : OmegaSpectrum.{u}) (k q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level k).space.right (q + 1) (X.level k).space.basepoint ≃*
      homotopyGroup X ((q : ℤ) + 2 - (k : ℤ)) := by
  have h := homotopyGroupEquivAt X ((q : ℤ) + 2 - (k : ℤ)) k (by omega)
  have hd : degree ((q : ℤ) + 2 - (k : ℤ)) k = q + 2 := by
    unfold degree
    omega
  rw [hd] at h
  exact h.symm

/-- 概要：有理化の各段の高次ホモトピー群は ℚ 加群。
方針：安定群の有理係数構造を任意段表示の加法同型で移す。
規約：q は実際の次数 q+2。零次数と一次群にはこの宣言を使わない。
使われ方：BF 1978 §2、Goerss–Jardine VIII §2。有限群 cochain の標数零係数。 -/
instance rationalizationLevelModule (X : OmegaSpectrum.{u}) (k q : ℕ) :
    Module ℚ (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((rationalization X).level k).space.right
      (q + 1) ((rationalization X).level k).space.basepoint)) :=
  (MulEquiv.toAdditive (positiveLevelStableEquiv (rationalization X) k q)).module ℚ

end

end SerrePositivity.KST.Spectra.OmegaSpectrum

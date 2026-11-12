module

public import SerrePositivity.KST.Spectra.OmegaSpectrumTransitions
public import SerrePositivity.KST.Spectra.LoopZeroHomotopy
public import Mathlib.Algebra.Group.TransferInstance

/-!
概要：Ω スペクトルの零次数の群と全自然数次数の段の比較。
方針：Ω 条件と π₀(ΩY)≃π₁(Y) で零次数へ次段の可換群構造を移す。
規約：正次数では構成済みの群演算を保持する。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の安定ホモトピー群。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：各段の連結成分は次段の基本群と同値。
方針：随伴構造射の零次数の同値と loop の零次数の同値を合成する。
規約：群構造を移す前の集合の同値。
使われ方：BF 1978 §2、HA §1.4.2。零次数の可換群。 -/
def zeroTransitionEquiv (X : OmegaSpectrum.{u}) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right 0 (X.level k).space.basepoint ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level (k + 1)).space.right 0 (X.level (k + 1)).space.basepoint := by
  let a := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level k).space (X.level (k + 1)).space) (X.sigma k)
  have ha : a.right.app _ (X.level k).space.basepoint =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (k + 1)).space).basepoint :=
    congrArg (fun g : 𝟙_ SSet.{u} ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (k + 1)).space).right ↦
      g.app _ PUnit.unit) (Under.w a)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism 0 a.right (X.omega_condition k) ha).trans
    (loopZeroHomotopyEquiv (X.level (k + 1)).space)

/-- 概要：各段の零次数の群は可換群。
方針：次段の基本群の可換群構造を零次数の比較同値で移す。
規約：元の連結成分の集合を基礎集合とする。
使われ方：BF 1978 §2、HA §1.4.2。安定ホモトピー群の零次数。 -/
instance levelZeroCommGroup (X : OmegaSpectrum.{u}) (k : ℕ) :
    CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right 0 (X.level k).space.basepoint) :=
  (zeroTransitionEquiv X k).commGroup

/-- 概要：零次数の比較同値を群同型として扱う。
方針：移送した演算が次段への同値で保たれることを計算する。
規約：零次数の演算はこの同値による移送。
使われ方：BF 1978 §2、HA §1.4.2。段の選択独立性。 -/
def zeroTransition (X : OmegaSpectrum.{u}) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right 0 (X.level k).space.basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level (k + 1)).space.right 0 (X.level (k + 1)).space.basepoint where
  toEquiv := zeroTransitionEquiv X k
  map_mul' _ _ := Equiv.apply_symm_apply _ _

/-- 概要：Ω スペクトルの全自然数次数の各段のホモトピー群は可換群。
方針：零次数の移送した群と正次数の既存の群をまとめる。
規約：自然数 n は実際の次数。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の群の構成。 -/
instance levelNaturalCommGroup (X : OmegaSpectrum.{u}) (k n : ℕ) :
    CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right n (X.level k).space.basepoint) := by
  cases n with
  | zero => exact levelZeroCommGroup X k
  | succ n => exact levelHomotopyCommGroup X k n

/-- 概要：全自然数次数で Ω スペクトルの隣接段の群を比較する。
方針：零次数の移送同型と正次数の連結群同型を次数でまとめる。
規約：π_n(X_k) と π_(n+1)(X_(k+1)) の群同型。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の群の段の選択独立性。 -/
def transition (X : OmegaSpectrum.{u}) (k n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right n (X.level k).space.basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level (k + 1)).space.right (n + 1) (X.level (k + 1)).space.basepoint := by
  cases n with
  | zero => exact zeroTransition X k
  | succ n => exact positiveTransition X k n

/-- 概要：零次数の比較は元の連結成分の基点を次段の基本群の単位へ送る。
方針：Ω 条件の基点保存と loop の零次数の基点の式を使う。
規約：群構造の移送の前の集合の同値の計算。
使われ方：BF 1978 §2、HA §1.4.2。元の基点と群の単位の照合。 -/
@[simp]
theorem zeroTransitionEquiv_point (X : OmegaSpectrum.{u}) (k : ℕ) :
    zeroTransitionEquiv X k (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0) = 1 := by
  dsimp only [zeroTransitionEquiv]
  rw [Equiv.trans_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_point, loopZeroHomotopyEquiv_point]

/-- 概要：各段の零次数の可換群の単位は元の基点。
方針：移送同値の単射性と基点の像の計算を使う。
規約：連結成分の基点を変更しない。
使われ方：BF 1978 §2、Kerodon §3.2.5（Tag 00WD）。完全列の群としての表示。 -/
theorem levelZero_one_eq_point (X : OmegaSpectrum.{u}) (k : ℕ) :
    (1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right 0 (X.level k).space.basepoint) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0 := by
  change (zeroTransitionEquiv X k).symm 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0
  apply (zeroTransitionEquiv X k).injective
  rw [Equiv.apply_symm_apply, zeroTransitionEquiv_point]

/-- 概要：全自然数次数で元の基点は各段の可換群の単位。
方針：零次数の移送の計算と正次数の定数単体の定義をまとめる。
規約：実際の次数 n。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の群と完全列の整合性。 -/
@[simp]
theorem levelPoint_eq_one (X : OmegaSpectrum.{u}) (k n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right n (X.level k).space.basepoint) = 1 := by
  cases n with
  | zero => exact (levelZero_one_eq_point X k).symm
  | succ n => rfl

end

end SerrePositivity.KST.Spectra.OmegaSpectrum

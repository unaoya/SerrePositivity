module

public import SerrePositivity.KST.Spectra.OmegaSpectrum
public import SerrePositivity.KST.Spectra.LoopHomotopyGroups

/-!
概要：Ω スペクトルの正次数の段の比較同型。
方針：随伴構造射の π_* 同型と loop の次数移動を合成する。
規約：零次数の段の比較はまだ主張しない。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の群の段の選択独立性。
-/

@[expose] public section

universe u

open CategoryTheory SSet MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω スペクトルの隣接段の正次数のホモトピー群は一つずれて同型。
方針：随伴構造射の誘導同型と loop の次数移動を使う。
規約：π_(n+1)(X_k) と π_(n+2)(X_(k+1)) を比較する。
使われ方：BF 1978 §2、HA §1.4.2。安定ホモトピー群の定義。 -/
def positiveTransition (X : OmegaSpectrum.{u}) (k n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level k).space.right n (X.level k).space.basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level (k + 1)).space.right (n + 1)
        (X.level (k + 1)).space.basepoint := by
  let a := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level k).space (X.level (k + 1)).space) (X.sigma k)
  have ha : a.right.app _ (X.level k).space.basepoint =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (k + 1)).space).basepoint :=
    congrArg (fun g : 𝟙_ SSet.{u} ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (k + 1)).space).right ↦
      g.app _ PUnit.unit) (Under.w a)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n a.right (X.omega_condition k) ha).trans
    (loopPositiveHomotopyEquiv (X.level (k + 1)).space n)

/-- 概要：Ω スペクトルの各段の全ての正次数のホモトピー群は可換。
方針：次段の一つ上の次数の群へ同型で移し、二以上の次数の可換性を使う。
規約：一次の群も含む。元の群演算を保つ。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の可換群の構成。 -/
theorem levelHomotopy_mul_comm (X : OmegaSpectrum.{u}) (k n : ℕ)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level k).space.right n (X.level k).space.basepoint) :
    a * b = b * a := by
  let e := positiveTransition X k n
  apply e.injective
  rw [e.map_mul, e.map_mul, mul_comm]

/-- 概要：Ω スペクトルの各段の正次数のホモトピー群の可換群構造。
方針：構成済みの群演算に次段への比較から得た可換性を付ける。
規約：零次数の集合にはまだ群を付けない。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の安定ホモトピー群。 -/
instance levelHomotopyCommGroup (X : OmegaSpectrum.{u}) (k n : ℕ) :
    CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level k).space.right n (X.level k).space.basepoint) where
  __ := (inferInstance :
    Group (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level k).space.right n (X.level k).space.basepoint))
  mul_comm := levelHomotopy_mul_comm X k n

end

end SerrePositivity.KST.Spectra.OmegaSpectrum

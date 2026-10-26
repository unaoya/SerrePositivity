module
public import SerrePositivity.KST.Fibration.ClosedKernelCoefficient
public import SerrePositivity.KST.Fibration.WeakStringFiniteAllLengths
public import SerrePositivity.KST.Fibration.WeakStringFinitePostMap

/-!
概要：元の P 内の全有限旗を、同じ P の初期頂点と全 cofiber 係数へ正規化する。
方針：既存 W 列の実有限比較へ元の全頂点同型と零化核の包含同型を後合成する。
規約：有限旗帰納を複製しない。使われ方：元の P 全旗包含の実積座標。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：元の P 全旗の指定初期頂点を同じ P 自身へ戻す完全評価。
方針：元の W 列評価へ全頂点の元の包含同型を合成する。
規約：同じ入力。使われ方：実初期評価四角形の第一辺。 -/
def closedKernelInitialExact (n : SimplexCategory) :
    weakStringModel (closedKernelZeroMap P) n ⟶ closedStableModel P :=
  weakStringVertexTopExact (closedKernelZeroMap P) n 0 ≫
    (closedTopExactIso (sInputModel (flagAmbient (closedStableModel P)))).hom

/-- 概要：元の P 内の全有限旗比較を元の P の全係数へ正規化する。
方針：同じ元の実有限比較の各係数へ厳密な包含同型を後合成する。
規約：商や retract 閉包を使わない。使われ方：引き戻した実積座標との照合。 -/
def closedKernelFiniteComparison (n r : ℕ) :
    (multiRealizationFunctor r).obj (weakStringModel (closedKernelZeroMap P) ⦋n⦌) ⟶
      (multiRealizationFunctor r).obj (closedStableModel P) ⊗
        ∏ᶜ fun _ : Fin n => (multiRealizationFunctor r).obj (closedStableModel P) :=
  weakStringFiniteComparison (closedKernelZeroMap P) n r ≫
    ((multiRealizationFunctor r).map
      (closedTopExactIso (sInputModel (flagAmbient (closedStableModel P)))).hom ⊗ₘ
      Limits.Pi.map (fun _ : Fin n => (multiRealizationFunctor r).map
        (closedFlagKernelCoefficientIso P).hom))

/-- 概要：同じ元の P 全旗比較は全長・全正反復で局所化同型。
方針：既存 q 版の全長比較と同じ元の全係数同型を合成する。
規約：実有限旗帰納を共有。使われ方：初期評価の引き戻しの源側座標。 -/
theorem closedKernelFiniteComparison_localized_isIso (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedKernelFiniteComparison P n (r + 1))) := by
  have := weakStringFiniteComparison_localized_isIso (closedKernelZeroMap P) n r
  unfold closedKernelFiniteComparison
  rw [Functor.map_comp]
  infer_instance

/-- 概要：元の P 全旗の初期評価四角形は元の包含を厳密に保持する。
方針：元の初期頂点と実後合成を全単体で計算する。
規約：商射を導入しない。使われ方：実積座標から引き戻しを移送する元の四角形。 -/
theorem closedKernelInitialPostSquare (n : SimplexCategory) (r : ℕ) :
    CommSq ((multiRealizationFunctor r).map (closedKernelInitialExact P n))
      ((multiRealizationFunctor r).map (closedKernelFlagPost P n))
      ((multiRealizationFunctor r).map (closedStableInclusion P))
      ((multiRealizationFunctor r).map (closedFlagVertex P n 0)) := by
  constructor
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (multiRealizationFunctor r).map
  apply Subtype.ext
  apply SSet.hom_ext
  intro k
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.KST.Fibration

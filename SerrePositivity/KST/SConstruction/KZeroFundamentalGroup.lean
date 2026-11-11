module
public import SerrePositivity.KST.SConstruction.KSpectrumConnectivity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-! # 実際の零次 K 群と一重 S の基本群
概要：元の BF K スペクトルの零次群を、一重 S の元の Kan 境界商の基本群と群同型で結ぶ。
方針：BF の零段表示・零段の遷移群同型・単射置換の一段の射影を合成する。
規約：loop と辺の向きの照合は別の計算式で行う。使われ方：cofiber の K 類の加法関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 元の K の零段群と、一重 S の Kan 境界商の実際の基本群の群同型。 -/
def kZeroLevelFundamentalGroupEquiv (X : StableModel.{u}) :
    OmegaSpectrum.levelHomotopy (kOmegaSpectrum X) 0 0 ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (((boundaryKanRealizationFunctor 0).obj X).right) 0
        ((boundaryKanRealizationFunctor 0).obj X).basepoint :=
  (OmegaSpectrum.zeroTransition (kOmegaSpectrum X) 0).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism 0 ((monicKKanSequenceProjection X).app 1).right
      (monicKKanSequenceProjection_piIsomorphism X 1)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ((monicKKanSequenceProjection X).app 1)))

/-- 実際の整数次数の零次 K 群と、一重 S の元の Kan 基本群の群同型。 -/
def kZeroFundamentalGroupEquiv (X : StableModel.{u}) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0 ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (((boundaryKanRealizationFunctor 0).obj X).right) 0
        ((boundaryKanRealizationFunctor 0).obj X).basepoint :=
  (kOmegaSpectrum_zeroGroupEquiv X).trans (kZeroLevelFundamentalGroupEquiv X)

/-- 一重 S の元の Kan 境界商の基本群の演算は可換。 -/
lemma boundaryFundamentalGroup_mul_comm (X : StableModel.{u})
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (((boundaryKanRealizationFunctor 0).obj X).right) 0
      ((boundaryKanRealizationFunctor 0).obj X).basepoint) : a * b = b * a := by
  apply (kZeroFundamentalGroupEquiv X).symm.injective
  rw [map_mul, map_mul, mul_comm]

end SerrePositivity.KST.SConstruction

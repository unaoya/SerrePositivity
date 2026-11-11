module
public import SerrePositivity.KST.SConstruction.KSpectrumConnectivity

/-! # 実際の BF K スペクトルの零次数と既存の K 空間
概要：BF K の零次数を、従来の零対象を選んだ K 空間の連結成分で計算する。
方針：元の零段の比較の全基点 π 同型と整数次数の零段表示を合成する。
規約：元の kSpace の定義を保つ。使われ方：π₀ K と TriangulatedK0 の対象類の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- BF K スペクトルの零次数と既存の K 空間の零次ホモトピー類の同値。 -/
def kOmegaSpectrum_zeroEquivKSpaceHomotopy (X : StableModel.{u}) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0 ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (kSpace X.carrier).right 0 (kSpace X.carrier).basepoint :=
  (kOmegaSpectrum_zeroGroupEquiv X).toEquiv.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism 0 (kSpaceSpectrumComparison X).right
      (kSpaceSpectrumComparison_piIsomorphism X)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (kSpaceSpectrumComparison X))).symm

/-- BF K スペクトルの零次数は既存の K 空間の連結成分で計算できる。 -/
def kOmegaSpectrum_zeroEquivKSpacePiZero (X : StableModel.{u}) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0 ≃ SSet.π₀ (kSpace X.carrier).right :=
  (kOmegaSpectrum_zeroEquivKSpaceHomotopy X).trans _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero

end SerrePositivity.KST.SConstruction

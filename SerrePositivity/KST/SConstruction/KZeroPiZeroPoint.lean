module
public import SerrePositivity.KST.SConstruction.KHomotopyZeroPiZero

/-! # 零次 K 群の単位と元の K 空間の定数 loop
概要：自然な零次 K 群の π₀ 表示は群の単位を元の定数 loop の成分へ送る。
方針：任意段表示の群同型と、置換射影の基点保存を用いる。
規約：実際の BF 群の単位を扱う。使われ方：零対象の K 類の零性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 零次 K 群の元の π₀ 表示は単位を定数 loop の成分へ送る。 -/
lemma kHomotopyZeroPiZeroEquiv_one (X : StableModel.{u}) :
    kHomotopyZeroPiZeroEquiv X 1 = SSet.π₀.mk (boundaryKSpaceFunctor.obj X).basepoint := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
    (pointedHomotopyMap 0 ((monicKKanSequenceProjection X).app 0)
      (OmegaSpectrum.homotopyGroupEquivAt (kOmegaSpectrum X) 0 0 _ 1)) = _
  rw [map_one, ← OmegaSpectrum.levelPoint_eq_one (kOmegaSpectrum X) 0 0,
    pointedHomotopyMap, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_point]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanComposite
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：元の零中間二胞体と指定全 S• 因子分解を、同じ実三次元内角へ貼り合わせる。
方針：公開 horn₃₂ の貼合せを、元の二胞体と二つの厳密合成二胞体に特殊化する。
規約：元の全二胞体を面 1 に保持する。一般中間対象輸送 API は新設しない。
使われ方：K-6 c4 の三角柱比較を構成する、元の二胞体を保つ実内角。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))

/-- 元の第一短辺を、同じ実 core 包含と全 S• 比較に厳密因子分解する実二胞体。 -/
def zeroMiddleFullSKanFirstTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (show stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩) ⟶
      fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (s.obj ⟨ULift.up 0⟩)))
    (zeroMiddleFullSKanComparison s hZ)

/-- 元の第二短辺と同じ全 S• 比較の厳密合成を保持する実二胞体。 -/
def zeroMiddleFullSKanLastTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (zeroMiddleFullSKanComparison s hZ)
    (stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 s)))

set_option maxHeartbeats 800000 in
-- 同じ core S と全 S• の対象座標を内角の三面で照合する。
/-- 元の二胞体を面 1 としてそのまま含む、同じ実全 S• 因子分解の内角。 -/
def zeroMiddleFullSKanHorn : (Λ[3, 2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := by
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌) s
  let F := zeroMiddleFullSKanFirstTriangle s hZ
  let L := zeroMiddleFullSKanLastTriangle s hZ
  refine horn₃₂.desc (SSet.yonedaEquiv.symm L.simplex) (SSet.yonedaEquiv.symm T)
    (SSet.yonedaEquiv.symm F.simplex) ?_ ?_ ?_
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
    apply congrArg SSet.yonedaEquiv.symm
    have he : (show stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩) ⟶
        fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (s.obj ⟨ULift.up 0⟩))) ≫
          zeroMiddleFullSKanComparison s hZ =
            stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s)) :=
      zeroMiddleFullSKanComparison_first s hZ
    have he' := congrArg (fun f : stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩) ⟶
        stableCoreSingleKanObject (s.obj ⟨ULift.up 1⟩) => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) he
    exact (zeroMiddleCoreSingleKanTriangle_first s).trans (he'.symm.trans F.d₁.symm)
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (L.d₂.trans F.d₀.symm)
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm
      (L.d₀.trans (zeroMiddleCoreSingleKanTriangle_last s).symm)

/-- 内角の面 1 は、元の native 二胞体の全二単体そのもの。 -/
theorem zeroMiddleFullSKanHorn_original :
    horn₃₂.ι₁ ≫ zeroMiddleFullSKanHorn s hZ =
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s) := by
  apply horn₃₂.ι₁_desc

end SerrePositivity.KST.Fibration

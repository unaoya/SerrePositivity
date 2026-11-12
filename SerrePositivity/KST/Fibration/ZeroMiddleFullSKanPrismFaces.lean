module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanPrism

/-!
概要：全 S• 中間対象の実三角柱の側面を、元の二つの厳密合成二胞体へ戻す。
方針：同じ内角の面 0・3 を充填の制限式で回収する。
規約：始端の二胞体を別の合成二胞体へ取り替えず、選択した実充填全体を保つ。
使われ方：K-6 c4 の点ごとの可逆性と、指定両短辺を持つ全三角柱比較。
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

/-- 同じ充填の面 3 は、元の第一短辺の厳密因子分解を持つ実二胞体。 -/
theorem zeroMiddleFullSKanTetrahedron_first :
    stdSimplex.δ (3 : Fin 4) ≫ zeroMiddleFullSKanTetrahedron s hZ =
      SSet.yonedaEquiv.symm (zeroMiddleFullSKanFirstTriangle s hZ).simplex := by
  calc
    _ = horn₃₂.ι₃ ≫ ((horn 3 (2 : Fin 4)).ι ≫
        zeroMiddleFullSKanTetrahedron s hZ) := by rw [← Category.assoc, horn.ι_ι]
    _ = horn₃₂.ι₃ ≫ zeroMiddleFullSKanHorn s hZ := by
      rw [← zeroMiddleFullSKanTetrahedron_horn]
    _ = _ := by apply horn₃₂.ι₃_desc

/-- 同じ充填の面 0 は、元の第二短辺との厳密合成を持つ実二胞体。 -/
theorem zeroMiddleFullSKanTetrahedron_last :
    stdSimplex.δ (0 : Fin 4) ≫ zeroMiddleFullSKanTetrahedron s hZ =
      SSet.yonedaEquiv.symm (zeroMiddleFullSKanLastTriangle s hZ).simplex := by
  calc
    _ = horn₃₂.ι₀ ≫ ((horn 3 (2 : Fin 4)).ι ≫
        zeroMiddleFullSKanTetrahedron s hZ) := by rw [← Category.assoc, horn.ι_ι]
    _ = horn₃₂.ι₀ ≫ zeroMiddleFullSKanHorn s hZ := by
      rw [← zeroMiddleFullSKanTetrahedron_horn]
    _ = _ := by apply horn₃₂.ι₀_desc

/-- 始端の第一短辺は、元の実 core 包含の同じ全一単体。 -/
theorem zeroMiddleFullSKanTransportedTriangle_first :
    stdSimplex.δ (2 : Fin 3) ≫ zeroMiddleFullSKanTransportedTriangle s hZ =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩) ⟶
          fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
            (coreSFullRealizationInclusion (s.obj ⟨ULift.up 0⟩)))).edge := by
  unfold zeroMiddleFullSKanTransportedTriangle
  erw [← Category.assoc, ← stdSimplex.δ_comp_δ (by decide : (2 : Fin 3) ≤ 2), Category.assoc,
    zeroMiddleFullSKanTetrahedron_first]
  exact (zeroMiddleFullSKanFirstTriangle s hZ).δ_two_yonedaEquiv_symm

end SerrePositivity.KST.Fibration

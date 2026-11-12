module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationInverseEdge
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
概要：零単体からの写像の連結成分と区間の端点の比較。
方針：Yoneda の同値で頂点へ移して π₀ の辺の関係を使う。
規約：Kan 性は不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。pullback 内の辺による成分の比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：零単体からの射をその頂点の連結成分へ送る。
方針：Yoneda の同値を通じて頂点を取り出す。
規約：標的は任意の単体集合。
使われ方：Kerodon §3.2.2（Tag 00VJ）。射の端点の等式を成分へ移す。 -/
def zeroMapComponent {X : SSet.{u}} (f : (Δ[0] : SSet.{u}) ⟶ X) : π₀ X :=
  π₀.mk (yonedaEquiv f)

/-- 概要：区間の両端点は同じ連結成分を与える。
方針：区間からの射の表す一単体を π₀ の辺の関係へ渡す。
規約：辺の向きは始点から終点。
使われ方：Goerss–Jardine I §7。連結写像の逆元の持ち上げの比較。 -/
theorem zeroMapComponent_edge {X : SSet.{u}} (r : (Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (stdSimplex.δ (1 : Fin 2) ≫ r) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (stdSimplex.δ (0 : Fin 2) ≫ r) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent, stdSimplex.yonedaEquiv_δ_comp] using
    π₀.sound (Edge.mk' (yonedaEquiv r))

/-- 概要：零単体の成分は標的の写像に関して自然。
方針：Yoneda の自然性で頂点の後合成を計算する。
規約：標的の Kan 性は不要。
使われ方：Kerodon §3.2.2（Tag 00VJ）。fiber から pullback へ成分を送る。 -/
theorem zeroMapComponent_comp {X Y : SSet.{u}}
    (f : (Δ[0] : SSet.{u}) ⟶ X) (g : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (f ≫ g) = mapπ₀ g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent f) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent, mapπ₀_mk]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.zeroMapComponent := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.zeroMapComponent_comp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.zeroMapComponent_edge := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.zeroMapComponent.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent.eq_1

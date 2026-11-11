module

public import SerrePositivity.KST.Spectra.RestrictionConnectingNullhomotopy
public import SerrePositivity.KST.Spectra.PointedZeroConnectingNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyComponents

/-!
概要：制限の零次数接続写像を相対商からの実際の射の成分で表す。
方針：任意の相対ホーン充填の最後の頂点を厳密な fiber 同型で戻す。
規約：元の入力の代表と、相対商の出力の射と、その nullhomotopy を保持する。
使われ方：Goerss–Jardine I §8、VIII §1。成分微分のセルごとの計算。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：源の単射の可換正方形で零次数接続写像は可換。
方針：標準の零次数自然性を源の前合成の正方形へ適用する。
規約：出力は零次数の集合。
使われ方：Goerss–Jardine VIII §1。成分微分をセル境界へ制限する。 -/
theorem restrictionSourceFiberMap_connectingZero {A B C D : SSet.{u}}
    (i : A ⟶ B) (j : C ⟶ D) [Mono i] [Mono j]
    (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ i = j ≫ b)
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj A Y).right 0 (obj A Y).basepoint) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 (restrictionSourceFiberMap i j a b h Y).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (restrictionSourceFiberMap i j a b h Y))
        (pointedConnectingZero (pre i Y) x) =
      pointedConnectingZero (pre j Y) (pointedGroupMap 0 (pre a Y) x) :=
  pointedConnectingZero_natural (pre i Y) (pre j Y) (pre b Y) (pre a Y)
    (pre_square i j a b h Y) x

/-- 源の正方形への零次数自然性を基点に依存しない成分へ移す。 -/
theorem restrictionSourceFiberMap_componentConnecting {A B C D : SSet.{u}}
    (i : A ⟶ B) (j : C ⟶ D) [Mono i] [Mono j]
    (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ i = j ≫ b)
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj A Y).right 0 (obj A Y).basepoint) :
    mapπ₀ (restrictionSourceFiberMap i j a b h Y).right
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (pointedConnectingZero (pre i Y) x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
        (pointedConnectingZero (pre j Y) (pointedGroupMap 0 (pre a Y) x)) := by
  have hn := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
    (restrictionSourceFiberMap_connectingZero i j a b h Y x)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map
    (restrictionSourceFiberMap i j a b h Y).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (restrictionSourceFiberMap i j a b h Y))
    (pointedConnectingZero (pre i Y) x)) = _ at hn
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map] at hn
  exact hn

/-- 概要：零次数接続写像の相対商表示は任意の充填からの実際の射の成分。
方針：標準接続写像の頂点公式と零次数から成分への自然性を使う。
規約：出力から基点への nullhomotopy の向きは既存の構成のまま。
使われ方：Goerss–Jardine VIII §1。局所的な成分微分の代表を固定する。 -/
theorem connectingZero_cofiberBoundaryMap {A B : SSet.{u}} (i : A ⟶ B)
    [Mono i] (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    {s : (obj A Y).right.PtSimplex 1 ((pre i Y).right.app _ (obj B Y).basepoint)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s) :
    mapπ₀ (restrictionFiberIso i Y).inv.right
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (pointedConnectingZero (pre i Y)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl (obj A Y).right)
            (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pre i Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)))) =
      π₀.mk (PointedMapping.familyVertex (cofiberBoundaryMap i Y L)) := by
  erw [pointedConnectingZero_boundaryLift (pre i Y) L]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map (restrictionFiberIso i Y).inv.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (restrictionFiberIso i Y).inv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary L))
  rw [← h]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk (cofiberBoundarySimplex i Y L)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, cofiberBoundaryMap, PointedMapping.familyVertex_familyMap]
  rfl

/-- 概要：任意の基本群入力の成分接続写像を相対商の射で代表できる。
方針：像の基点へ戻して入力単体を選び、実際に相対ホーンを充填する。
規約：元の入力との等式を結論に含め、出力だけの代表の存在へ弱めない。
使われ方：Goerss–Jardine VIII §1。全ての係数を局所の代表計算へ渡す。 -/
theorem exists_connectingZero_boundaryRepresentative {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj A Y).right 0 (obj A Y).basepoint) :
    ∃ (s : (obj A Y).right.PtSimplex 1 ((pre i Y).right.app _ (obj B Y).basepoint))
      (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s),
      a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl (obj A Y).right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pre i Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) ∧
        mapπ₀ (restrictionFiberIso i Y).inv.right
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (pointedConnectingZero (pre i Y) a)) =
          π₀.mk (PointedMapping.familyVertex (cofiberBoundaryMap i Y L)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl (obj A Y).right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pre i Y))
  obtain ⟨s, hs⟩ := Quotient.mk_surjective (e.symm a)
  have ha : a = e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) := by
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = e.symm a from hs, MulEquiv.apply_symm_apply]
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift (pre i Y).right (obj B Y).basepoint s
  refine ⟨s, L, ha, ?_⟩
  rw [ha]
  exact connectingZero_cofiberBoundaryMap i Y L

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping

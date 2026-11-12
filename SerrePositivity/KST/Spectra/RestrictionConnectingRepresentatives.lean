module

public import SerrePositivity.KST.Spectra.PointedConnectingRepresentatives
public import SerrePositivity.KST.Spectra.RestrictionSourceSquare

/-!
概要：制限写像の連結射の代表を相対商からの写像空間へ移す。
方針：相対ホーン充填の最後の面を厳密な fiber 同型で戻し、元の写像空間で評価する。
規約：代表の単体の射と基点を明示し、群の零性へ弱めない。
使われ方：Goerss–Jardine I §8、VIII §1。局所的なセルの連結射の値と向きの計算。
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

variable {A B : SSet.{u}} (i : A ⟶ B) (Y : PointedSimplicialSet.{u})

@[reassoc]
lemma restrictionFiberIso_inv_projection :
    (restrictionFiberIso i Y).inv ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
          (pointedCofiberProjection (PointedObject.adjoinFunctor.map i)) Y ≫
        (freeHomIso B Y).hom = pointedFiberι (pre i Y) := by
  have h := congrArg (fun f ↦ (restrictionFiberIso i Y).inv ≫ f)
    (restrictionFiberIso_hom_ι i Y)
  simpa only [Iso.inv_hom_id_assoc, Category.assoc] using h.symm

/-- 概要：制限の相対ホーン充填から相対商の写像空間の境界定数単体を作る。
方針：最後の面を標準基点の fiber へ移し、相対商による fiber 表示の逆射を適用する。
規約：充填の選択は任意。次数 n は零も許す。
使われ方：Goerss–Jardine VIII §1。局所的な連結射の球面写像による代表。 -/
def cofiberBoundarySimplex {n : ℕ}
    {s : (obj A Y).right.PtSimplex (n + 1) ((pre i Y).right.app _ (obj B Y).basepoint)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s) :
    (PointedObject.basedHom (relativeSource i) Y).right.PtSimplex n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom (relativeSource i) Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (restrictionFiberIso i Y).inv.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (restrictionFiberIso i Y).inv) (_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary L)

/-- 概要：相対商の代表を元の写像空間へ戻すと指定した充填の最後の面。
方針：fiber 表示の逆射の射影式と最後の面の包含公式を合成する。
規約：単体の射そのものの等式。
使われ方：Goerss–Jardine I §8、VIII §1。符号を計算する実際のパラメータ族。 -/
@[reassoc]
lemma cofiberBoundarySimplex_projection {n : ℕ}
    {s : (obj A Y).right.PtSimplex (n + 1) ((pre i Y).right.app _ (obj B Y).basepoint)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s) :
    (cofiberBoundarySimplex i Y L).map ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
          (pointedCofiberProjection (PointedObject.adjoinFunctor.map i)) Y).right ≫
        (freeHomIso B Y).hom.right = stdSimplex.δ (Fin.last (n + 1)) ≫ L.map := by
  have h := congrArg Under.Hom.right (restrictionFiberIso_inv_projection i Y)
  change (restrictionFiberIso i Y).inv.right ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
      (pointedCofiberProjection (PointedObject.adjoinFunctor.map i)) Y).right ≫
      (freeHomIso B Y).hom.right = (pointedFiberι (pre i Y)).right at h
  change ((_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary L).map ≫ (restrictionFiberIso i Y).inv.right) ≫ _ ≫ _ = _
  rw [Category.assoc, h]
  exact (_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary_ι L)

/-- 概要：連結準同型の相対商表示は任意の充填から作った単体の類。
方針：標準基点での連結射の代表公式を相対商の写像空間へ送る。
規約：底の代表の基点を標準基点へ移す操作を左辺に明示する。
使われ方：Goerss–Jardine VIII §1。実際の連結射と球面の向きの代表レベルの比較。 -/
theorem connectingHom_cofiberBoundarySimplex [Mono i] [KanComplex Y.right] (r : ℕ)
    {s : (obj A Y).right.PtSimplex (r + 2) ((pre i Y).right.app _ (obj B Y).basepoint)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s) :
    pointedGroupMap r (restrictionFiberIso i Y).inv
        (pointedConnectingHom (pre i Y) r
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl (obj A Y).right)
            (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pre i Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (cofiberBoundarySimplex i Y L) := by
  erw [pointedConnectingHom_boundaryLift (pre i Y) r L]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk _ _ _

/-- 概要：任意の正次数の入力の連結射を実際の充填と最後の面で代表できる。
方針：基点を戻した入力の単体を選び、Kan fibration の相対ホーンを充填する。
規約：入力との対応の等式も保持する。単なる出力の代表の存在へ弱めない。
使われ方：Goerss–Jardine VIII §1。任意の係数に対する局所連結射の実計算。 -/
theorem exists_connecting_boundaryRepresentative [Mono i] [KanComplex Y.right] (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj A Y).right (r + 1) (obj A Y).basepoint) :
    ∃ (s : (obj A Y).right.PtSimplex (r + 2)
        ((pre i Y).right.app _ (obj B Y).basepoint))
      (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s),
      a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl (obj A Y).right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pre i Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) ∧
        pointedGroupMap r (restrictionFiberIso i Y).inv (pointedConnectingHom (pre i Y) r a) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (cofiberBoundarySimplex i Y L) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl (obj A Y).right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pre i Y))
  obtain ⟨s, hs⟩ := Quotient.mk_surjective (e.symm a)
  have ha : a = e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) := by
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = e.symm a from hs, MulEquiv.apply_symm_apply]
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift (pre i Y).right (obj B Y).basepoint s
  refine ⟨s, L, ha, ?_⟩
  rw [ha]
  exact connectingHom_cofiberBoundarySimplex i Y r L

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping

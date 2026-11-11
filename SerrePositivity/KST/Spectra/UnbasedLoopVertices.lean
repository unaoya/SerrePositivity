module

public import SerrePositivity.KST.Spectra.PointedExchangeVertices
public import SerrePositivity.KST.Spectra.UnbasedLoopSwap
public import SerrePositivity.KST.Spectra.UnbasedMapVertices
public import SerrePositivity.KST.Spectra.UnbasedLoopFamilies
public import SerrePositivity.KST.Spectra.LoopPathVertices
public import SerrePositivity.KST.Spectra.LoopZeroOrientation

/-!
概要：通常の loop 値の射を交換同型で写像空間の loop の頂点へ送る。
方針：自由基点を加え、点つき転置の頂点公式と自由 Hom の同型を合成する。
規約：標的の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。骨格の接続写像の入力の比較。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- loop 値の通常の射を転置した、円から写像空間への点つき射。 -/
def loopFamilyMap {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) : PointedSimplicialSet.circle.{u} ⟶ obj A Y :=
  PointedMapping.exchangeMap ((PointedObject.adjoinHomEquiv A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).symm f) ≫
    (freeHomIso A Y).hom

/-- 転置した円の射を通常の指数として読む評価式。 -/
lemma loopFamilyMap_right {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) :
    (loopFamilyMap Y f).right =
      curry ((β_ A PointedSimplicialSet.circle.right).hom ≫
        uncurry (f ≫ PointedObject.basedHomι PointedSimplicialSet.circle Y)) := by
  change (PointedMapping.exchangeMap _).right ≫
    (PointedObject.basedHomι (PointedObject.adjoin A) Y ≫
      (MonoidalClosed.pre coprod.inl).app Y.right) = _
  rw [← Category.assoc, PointedMapping.exchangeMap_ι, curry_pre_app]
  apply congrArg curry
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
    ← uncurry_natural_left, ← Category.assoc]
  change (β_ A PointedSimplicialSet.circle.right).hom ≫
    uncurry ((PointedObject.adjoinHomEquiv A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))
      ((PointedObject.adjoinHomEquiv A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).symm f) ≫
        PointedObject.basedHomι PointedSimplicialSet.circle Y) = _
  rw [Equiv.apply_symm_apply]

/-- 円の射の標準区間上での評価は、既存の loop 族の辺そのもの。 -/
lemma loopFamilyMap_interval {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) :
    PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫ (loopFamilyMap Y f).right =
      (loopFamilySimplex Y f).map := by
  rw [loopFamilyMap_right, ← curry_natural_left]
  change curry (_ ≫ (β_ A PointedSimplicialSet.circle.right).hom ≫ _) =
    pathFamilyEdge Y (f ≫ (PointedMapping.loopToPath Y).right)
  erw [BraidedCategory.braiding_naturality_right_assoc]
  rw [pathFamilyEdge, loopToPath_eq_pre, Category.assoc]
  change _ = curry ((β_ A (Δ[1] : SSet.{u})).hom ≫
    uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre circleIntervalProjection Y ≫
      PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y))
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι]
  have he := uncurry_pre_app Y.right
    (f ≫ PointedObject.basedHomι PointedSimplicialSet.circle Y)
    circleIntervalProjection.right
  rw [Category.assoc] at he
  conv at he => rhs; rw [circleIntervalProjection_right]
  have hc := congrArg (fun g ↦ curry ((β_ A (Δ[1] : SSet.{u})).hom ≫ g)) he
  exact hc.symm

/-- 円からの転置を単体へ戻すと、指定した loop の辺を回収する。 -/
lemma loopFamilyMap_toSimplex {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) :
    SphereSimplex.equiv (obj A Y) 1 (loopFamilyMap Y f) = loopFamilySimplex Y f := by
  ext : 1
  exact loopFamilyMap_interval Y f

/-- loop 交換の逆射は通常の射の頂点を転置した円の射の頂点へ送る。 -/
lemma loopSwap_inv_mapVertex {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) :
    (loopSwap A Y).inv.right.app _ (mapVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f) =
      PointedMapping.familyVertex (loopFamilyMap Y f) := by
  let g := (PointedObject.adjoinHomEquiv A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).symm f
  rw [← freeHomIso_familyVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f]
  change (PointedObject.basedHomMap PointedSimplicialSet.circle (freeHomIso A Y).hom).right.app _
    ((PointedMapping.loopSwap (PointedObject.adjoin A) Y).inv.right.app _
      ((freeHomIso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).inv.right.app _
        ((freeHomIso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).hom.right.app _ (PointedMapping.familyVertex g)))) = _
  have hi : (freeHomIso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).inv.right.app _
      ((freeHomIso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).hom.right.app _ (PointedMapping.familyVertex g)) =
      PointedMapping.familyVertex g := by
    change ((freeHomIso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).hom ≫
      (freeHomIso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).inv).right.app _ _ = _
    rw [Iso.hom_inv_id]
    rfl
  rw [hi, PointedMapping.loopSwap_inv_familyVertex, PointedMapping.familyVertex_post]
  rfl

/-- 標準の零 loop 比較で通常の射の頂点を送ると、明示した loop 族の逆辺の類。 -/
lemma loopZero_mapVertex {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) :
    loopZeroHomotopyEquiv (obj A Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm
      (mapπ₀ (loopSwap A Y).inv.right (π₀.mk (mapVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f)))) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (loopFamilySimplex Y f))⁻¹ := by
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm
      (mapπ₀ (loopSwap A Y).inv.right (π₀.mk (mapVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 ((PtSimplex.equiv₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (obj A Y)).basepoint).symm
        (PointedMapping.familyVertex (loopFamilyMap Y f))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.injective
    rw [Equiv.apply_symm_apply]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk _)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, Equiv.apply_symm_apply,
      mapπ₀_mk, loopSwap_inv_mapVertex]
  rw [hz, loopZeroHomotopyEquiv_familyVertex, loopFamilyMap_toSimplex]

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping

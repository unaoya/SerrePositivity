module
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison

/-! # 同じ元の随伴の二つの Kan 延長の比較
概要：元の射を単位上で回収する二つの随伴延長は、前向き Kan 比較で成分が可換。
方針：源の同じ anodyne 単位に沿う延長の一意性を適用する。
規約：標準点つき対象の実単位を使う。使われ方：旧 SOA・新 Ex∞ 組み立ての比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open Spectra.PointedMapping

/-- 同じ loop の Kan 性を標準 basedHom 関手の型で保持する。 -/
local instance soaExInfinityAdjointLoop_kanComplex (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] :
    KanComplex ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).obj Y).right :=
  loopSpace_kanComplex Y

/-- 同じ元の射を回収する旧・新随伴は、前向き Kan 比較で点つき成分が可換。 -/
lemma soaExInfinityAdjoint_component (U B : PointedSSetObject.{u})
    (a : U.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B.obj)
    (old : PointedKanReplacement.obj U.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedKanReplacement.obj B.obj))
    (new : (exInfinityPointedKanEnrichedFunctor.obj U).obj ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (exInfinityPointedKanEnrichedFunctor.obj B).obj)
    (ho : PointedKanReplacement.unit.app U.obj ≫ old = a ≫
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
        (PointedKanReplacement.unit.app B.obj))
    (hn : exInfinityPointedUnit U ≫ new = a ≫
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
        (exInfinityPointedUnit B)) :
    componentOf (pointedSOAExInfinityComparison U ≫ new) =
      componentOf (old ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
          (pointedSOAExInfinityComparison B)) := by
  let L := PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}
  obtain ⟨e⟩ := pointedExtensions_nonempty_mappingEdge
    (PointedKanReplacement.unit.app U.obj) (PointedKanReplacement.unit_anodyne U.obj)
    (a ≫ L.map (exInfinityPointedUnit B))
    (pointedSOAExInfinityComparison U ≫ new)
    (old ≫ L.map (pointedSOAExInfinityComparison B)) (by
      erw [← Category.assoc, pointedSOAExInfinityComparison_unit, hn]) (by
      erw [← Category.assoc, ho, Category.assoc, ← L.map_comp,
        pointedSOAExInfinityComparison_unit])
  exact SSet.π₀.sound e

end SerrePositivity.KST.SConstruction

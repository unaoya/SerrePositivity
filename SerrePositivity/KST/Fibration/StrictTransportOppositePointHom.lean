module
public import SerrePositivity.KST.Fibration.KanEnrichedOppositePointHom
public import SerrePositivity.InfinityCategories.Stable.Transport.StrictTransportOppositeEvaluation

/-! # 元の strict transport の反転比較の指定成分が、元の係数点の射を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  (p : E ⟶ nerve I) [LeftFibration p]

/-- 既存の strict transport 比較の同じ成分は、元の大域反転同型の成分そのもの。 -/
theorem strictTransportOppositeComponentIso_eq_enriched (i : I) :
    _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso p i =
      _root_.SerrePositivity.InfinityCategories.Stable.KanModels.kanEnrichedOppositeComponentIso (relativeSectionEnrichedDiagram (strictTransportDomains I))
        (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p) i := by
  let D := relativeSectionEnrichedDiagram (strictTransportDomains I)
  let X := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p
  let T := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X i
  have hm := F2.vertexIso_map_heq_of_heq (leftStraighteningCoherentMap_oppositeIso I)
    D.oppositeRealizationIso
    (congrArg functorVertex (congrArg
      (fun F => edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve I)) ≫ F)
      (strictTransportDomains_realization I).symm)) rfl
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeIso_heq (I := I)) T
  have hn : HEq (_root_.SerrePositivity.InfinityCategories.Stable.KanModels.kanEnrichedOppositeComponentIso D X i)
      (VertexIso.map D.oppositeRealizationIso T) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_precomp_vertex D
          (edgewiseEnrichedRight (LeftFibrationObject (nerve I))) X i))
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_vertex D.opposite X i))
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso_heq_doubleMap p i).trans
    (hm.trans hn.symm))

/-- 既存の同じ指定反転成分は、元の係数点を反転側の同じ点へ送る。 -/
theorem strictTransportOppositeComponentIso_pointHom (i : I)
    (v : (leftStrictTransport p i) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor p).obj i)).symm v) ≫
        (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso p i).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv
        (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj i))).symm
          (SSet.opObjEquiv.symm v)) := by
  rw [strictTransportOppositeComponentIso_eq_enriched]
  exact kanEnrichedOppositeComponentIso_pointHom
    (relativeSectionEnrichedDiagram (strictTransportDomains I))
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p) i v

end SerrePositivity.KST.Fibration

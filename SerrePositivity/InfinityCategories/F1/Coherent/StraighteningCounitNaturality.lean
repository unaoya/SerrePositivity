module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationComparisonRestriction
public import SerrePositivity.InfinityCategories.F1.Coherent.StraighteningCounitRestriction

/-!
概要：選択した余単位の底変換に関する自然性の可換式。
方針：cartesian な比較を通常の前合成と同定し表現空間の三角形を使う。
規約：全図式と全空間を保つ同じ比較を用いる。
使われ方：普遍余単位と任意の族への制限の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：余単位の cartesian 制限は通常の前合成による余単位と一致する。
方針：標準表現の制限を回収し図式同型の前合成の公式を使う。
規約：終点の図式の等式の移送を明示する。
使われ方：底変換に関する余単位の可換式の右辺。 -/
lemma coherentStraighteningRestrictedCounit_diagram {B D : SSet.{u + 1}}
    (F : D ⟶ SpaceInfinity.{u}) (G : B ⟶ SpaceInfinity.{u})
    (g : D ⟶ B) (h : g ≫ G = F) :
    (coherentStraighteningRestrictedRepresentation F G g h).diagramIso
      (unstraighteningTransportRepresentation F)
      (coherentStraighteningRestrictedCounitWitnessIso F G g h) =
      (coherentStraighteningCounit G).precomp g ≪≫
        eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d)) h) := by
  dsimp only [coherentStraighteningRestrictedCounitWitnessIso]
  rw [LeftTransportRepresentation.diagramIso_trans,
    LeftTransportRepresentation.diagramIso_eqToIso
      ((unstraighteningTransportRepresentation G).cartesianRestrict
        (leftUnstraighteningMap F G g h) g (leftUnstraighteningMap_isPullback F G g h))
      (unstraighteningTransportRepresentation F)
      (unstraighteningTransportRepresentation_cartesianRestrict F G g h)]
  let R := smallFiberLeftStraighteningRepresentation (leftUnstraighteningProjection G)
    (leftUnstraighteningProjection_hasSmallSimplexFibers G)
  let S := unstraighteningTransportRepresentation G
  let a := smallFiberTransportRepresentationVertexIso (leftUnstraighteningProjection G)
    (leftUnstraighteningProjection_hasSmallSimplexFibers G) R S
  have he := R.cartesianRestrict_diagramIso S a (leftUnstraighteningMap F G g h) g
    (leftUnstraighteningMap_isPullback F G g h)
  exact congrArg (fun e : FunctorIso (g ≫ R.diagram) (g ≫ G) ↦
    e ≪≫ eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d)) h)) he

/-- 概要：選択した余単位は分類の制限比較と通常の前合成に関して可換。
方針：表現空間で証明した三角形の二番目の辺を前合成で表示する。
規約：任意の底と底の射に適用し小ささを追加しない。
使われ方：単位・余単位の自然性の底変換側の界面。 -/
lemma coherentStraighteningCounit_baseChange_naturality {B D : SSet.{u + 1}}
    (F : D ⟶ SpaceInfinity.{u}) (G : B ⟶ SpaceInfinity.{u})
    (g : D ⟶ B) (h : g ≫ G = F) :
    coherentStraighteningRestrictionDiagramIso F G g h ≪≫
      (coherentStraighteningCounit G).precomp g ≪≫
        eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d)) h) =
      coherentStraighteningCounit F := by
  rw [← coherentStraighteningRestrictedCounit_diagram F G g h]
  exact coherentStraighteningCounitRestriction_diagram_triangle F G g h

end SerrePositivity.InfinityCategories

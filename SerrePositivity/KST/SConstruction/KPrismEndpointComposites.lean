module
public import SerrePositivity.KST.SConstruction.CoherentPrismDirectTriangles
public import SerrePositivity.KST.SConstruction.CoherentTriangleFullPathValues
public import SerrePositivity.KST.SConstruction.CoherentNativeValueTransport
public import SerrePositivity.KST.SConstruction.CoherentNativeContractionEdges
public import SerrePositivity.KST.SConstruction.KPrismSpanEndpointsConstant
public import SerrePositivity.KST.SConstruction.KSuspensionMappingTriangles

/-! # 元の K prism の定数終点は元の二合成
概要：上下の短い因子分解列を元の square の二三角形に照合し、定数終点を元の二合成へ同定する。
方針：同じ標準三角形の Path 評価と対象等式の移送を依存等号で比較する。
規約：零段を含む元の構造射・段の写像・全円柱を保持する。
使われ方：既存 BF 写像の境界と射影を保つ coherent な厳密化へ元の二円柱を渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismEndpointComposites_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 下側の元の二辺の豊穣単体は、元の square の同じ指定三角形。 -/
lemma kKanOriginalPrismLowerDirect_cell {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋2⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)).chain) =
      (kKanSuspensionMappingTriangles r F f).bottomRight.simplex := by
  change (kKanOriginalSuspensionHomotopy F r).h.app _
      ((coherentOrdinaryPrismIso.{u, u + 1} I).hom.app _
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)).chain)) =
    (kKanOriginalSuspensionHomotopy F r).h.app _
      ((SSet.yonedaEquiv.symm (ULift.up (nerve.edgeMk f).edge) ▷
        (Δ[1] : SSet.{u + 1})).app (Opposite.op ⦋2⦌)
        (((SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
          (SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).simplex))
  exact congrArg ((kKanOriginalSuspensionHomotopy F r).h.app (Opposite.op ⦋2⦌))
    (coherentLowerPrismDirect_forward.{u, u + 1} f)

/-- 元の suspension 写像空間の下側の終点は、元の短い列の同じ Path 評価である。 -/
lemma kKanOriginalPrismLowerEndpointVertex_raw_heq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    HEq (kKanOriginalPrismLowerEndpointVertex r F f)
      ((((kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋2⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)).chain)).map
          (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString
              (coherentArrowStringDirect f))))) := by
  have hv : kKanOriginalPrismLowerEndpointVertex r F f =
      (kKanOriginalPrismNativeHomIso r F x y).hom.app (Opposite.op ⦋0⦌)
        ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f))).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString
              (coherentArrowStringDirect f))))) := by
    change (kKanOriginalPrismNativeHomIso r F x y).hom.app _
      ((coherentPrismLowerNativeFamily (kKanOriginalPrismStringDiagram r F) f).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))) = _
    rw [coherentPrismLowerNativeFamily_vertex]
  have ht := coherentEqToHom_value_heq
    (congrArg₂ (fun A B : PointedSimplicialSet.{u} => (PointedObject.basedHom A B).right)
      (kKanOriginalPrismStringVertex_bottom r F x) (kKanOriginalPrismStringVertex_top r F y))
    ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f))).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString
          (coherentArrowStringDirect f)))))
  exact hv.heq.trans (ht.trans
    (coherentStringNativeMap_value_heq (kKanOriginalPrismStringDiagram r F)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)) _))

/-- 上側の元の二辺の豊穣単体は、元の square の同じ指定三角形。 -/
lemma kKanOriginalPrismUpperDirect_cell {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋2⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)).chain) =
      (kKanSuspensionMappingTriangles r F f).leftTop.simplex := by
  change (kKanOriginalSuspensionHomotopy F r).h.app _
      ((coherentOrdinaryPrismIso.{u, u + 1} I).hom.app _
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)).chain)) =
    (kKanOriginalSuspensionHomotopy F r).h.app _
      ((SSet.yonedaEquiv.symm (ULift.up (nerve.edgeMk f).edge) ▷
        (Δ[1] : SSet.{u + 1})).app (Opposite.op ⦋2⦌)
        (((SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
          (SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).simplex))
  exact congrArg ((kKanOriginalSuspensionHomotopy F r).h.app (Opposite.op ⦋2⦌))
    (coherentUpperPrismDirect_forward.{u, u + 1} f)

/-- 元の suspension 写像空間の上側の終点は、元の短い列の同じ Path 評価である。 -/
lemma kKanOriginalPrismUpperEndpointVertex_raw_heq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    HEq (kKanOriginalPrismUpperEndpointVertex r F f)
      ((((kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋2⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)).chain)).map
          (.mk (ULift.up 0)) (.mk (ULift.up 2))).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString
              (coherentArrowStringDirect f))))) := by
  have hv : kKanOriginalPrismUpperEndpointVertex r F f =
      (kKanOriginalPrismNativeHomIso r F x y).hom.app (Opposite.op ⦋0⦌)
        ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f))).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString
              (coherentArrowStringDirect f))))) := by
    change (kKanOriginalPrismNativeHomIso r F x y).hom.app _
      ((coherentPrismUpperNativeFamily (kKanOriginalPrismStringDiagram r F) f).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))) = _
    rw [coherentPrismUpperNativeFamily_vertex]
  have ht := coherentEqToHom_value_heq
    (congrArg₂ (fun A B : PointedSimplicialSet.{u} => (PointedObject.basedHom A B).right)
      (kKanOriginalPrismStringVertex_bottom r F x) (kKanOriginalPrismStringVertex_top r F y))
    ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f))).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString
          (coherentArrowStringDirect f)))))
  exact hv.heq.trans (ht.trans
    (coherentStringNativeMap_value_heq (kKanOriginalPrismStringDiagram r F)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)) _))

/-- 下側の定数終点は、元の構造射と元の段の写像の明示的な合成の頂点。 -/
lemma kKanOriginalPrismLowerEndpointVertex_composite {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismLowerEndpointVertex r F f =
      PointedMapping.familyVertex (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
        (kKanSequence (F.obj y)).sigma r) := by
  let p := coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f))
  have hp : (ULift.up 1 : ULift.{u} (Fin 3)) ∈ p.I := Set.mem_univ _
  have ht := coherentTrianglePath_value_heq (kKanOriginalPrismLowerDirect_cell r F f) p
  have hv := coherentTrianglePath_specified_composite_heq
    (kKanSuspensionMappingTriangles r F f).bottomRight p hp
  have h := (kKanOriginalPrismLowerEndpointVertex_raw_heq r F f).trans (ht.trans hv)
  exact (eq_of_heq h).trans (PointedMapping.familyVertex_eq_pointedHomVertex _).symm

/-- 上側の定数終点は、元の構造射と元の段の写像の明示的な合成の頂点。 -/
lemma kKanOriginalPrismUpperEndpointVertex_composite {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismUpperEndpointVertex r F f =
      PointedMapping.familyVertex ((kKanSequence (F.obj x)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1)) := by
  let p := coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f))
  have hp : (ULift.up 1 : ULift.{u} (Fin 3)) ∈ p.I := Set.mem_univ _
  have ht := coherentTrianglePath_value_heq (kKanOriginalPrismUpperDirect_cell r F f) p
  have hv := coherentTrianglePath_specified_composite_heq
    (kKanSuspensionMappingTriangles r F f).leftTop p hp
  have h := (kKanOriginalPrismUpperEndpointVertex_raw_heq r F f).trans (ht.trans hv)
  exact (eq_of_heq h).trans (PointedMapping.familyVertex_eq_pointedHomVertex _).symm

/-- 下側の全終点族は、元の明示的な二合成の定数族そのもの。 -/
lemma kKanOriginalPrismLowerSuspensionFamily_composite {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismLowerSuspensionFamily r F f =
      SSet.const (PointedMapping.familyVertex (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
        (kKanSequence (F.obj y)).sigma r)) :=
  (kKanOriginalPrismLowerSuspensionFamily_eq_const r F f).trans
    (congrArg (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)))
      (kKanOriginalPrismLowerEndpointVertex_composite r F f))

/-- 元の長辺から下側の明示的な二合成へ向かう、全精密化パラメータ上の同じ実円柱。 -/
def kKanOriginalPrismLowerCompositeContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f))
      (kKanOriginalPrismSpanInitialVertex r F f))
      (SSet.const (PointedMapping.familyVertex (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
        (kKanSequence (F.obj y)).sigma r))) := by
  let H := kKanOriginalPrismLowerSuspensionContraction r F f
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁.trans (kKanOriginalPrismLowerSuspensionFamily_composite r F f)
      rel := H.rel }

/-- 二合成を明示しても、元の下側の全時刻の円柱を厳密に保持する。 -/
lemma kKanOriginalPrismLowerCompositeContraction_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismLowerCompositeContraction r F f).h =
      (kKanOriginalPrismLowerSuspensionContraction r F f).h := rfl

/-- 上側の全終点族は、元の明示的な二合成の定数族そのもの。 -/
lemma kKanOriginalPrismUpperSuspensionFamily_composite {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismUpperSuspensionFamily r F f =
      SSet.const (PointedMapping.familyVertex ((kKanSequence (F.obj x)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1))) :=
  (kKanOriginalPrismUpperSuspensionFamily_eq_const r F f).trans
    (congrArg (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)))
      (kKanOriginalPrismUpperEndpointVertex_composite r F f))

/-- 元の長辺から上側の明示的な二合成へ向かう、全精密化パラメータ上の同じ実円柱。 -/
def kKanOriginalPrismUpperCompositeContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f))
      (kKanOriginalPrismSpanInitialVertex r F f))
      (SSet.const (PointedMapping.familyVertex ((kKanSequence (F.obj x)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1)))) := by
  let H := kKanOriginalPrismUpperSuspensionContraction r F f
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁.trans (kKanOriginalPrismUpperSuspensionFamily_composite r F f)
      rel := H.rel }

/-- 二合成を明示しても、元の上側の全時刻の円柱を厳密に保持する。 -/
lemma kKanOriginalPrismUpperCompositeContraction_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismUpperCompositeContraction r F f).h =
      (kKanOriginalPrismUpperSuspensionContraction r F f).h := rfl

/-- 元の入力射の指定頂点で、下側の同じ実円柱は元の Path 包含辺を厳密に回収する。 -/
lemma kKanOriginalPrismLowerCompositeContraction_vertex_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanOriginalPrismLowerCompositeContraction r F f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))).edge =
      (kKanOriginalPrismNativeHomIso r F x y).hom.app (Opposite.op ⦋1⦌)
        ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f))).app (Opposite.op ⦋1⦌)
            (nerve.edgeMk (coherentStringRefinementPathToFull
              (coherentArrowStringDirectTo
                (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f))))).edge) := by
  have hv : (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)) :=
    ComposableArrows.ext₀ rfl
  exact coherentArrowNativeContraction_prepost_vertex_edge
    (kKanOriginalPrismStringDiagram r F) (coherentPrismArrow f)
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f)) (kKanOriginalPrismNativeHomIso r F x y).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)) hv

/-- 元の入力射の指定頂点で、上側の同じ実円柱は元の Path 包含辺を厳密に回収する。 -/
lemma kKanOriginalPrismUpperCompositeContraction_vertex_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanOriginalPrismUpperCompositeContraction r F f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))).edge =
      (kKanOriginalPrismNativeHomIso r F x y).hom.app (Opposite.op ⦋1⦌)
        ((coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f))).app (Opposite.op ⦋1⦌)
            (nerve.edgeMk (coherentStringRefinementPathToFull
              (coherentArrowStringDirectTo
                (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f))))).edge) := by
  have hv : (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)) :=
    ComposableArrows.ext₀ rfl
  exact coherentArrowNativeContraction_prepost_vertex_edge
    (kKanOriginalPrismStringDiagram r F) (coherentPrismArrow f)
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f)) (kKanOriginalPrismNativeHomIso r F x y).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)) hv

end SerrePositivity.KST.SConstruction

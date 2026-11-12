module
public import SerrePositivity.KST.SConstruction.KCompositionPrismSquares
public import SerrePositivity.KST.SConstruction.CoherentTetrahedronSpecifiedFaces

/-! # 元の K 合成 prism の残る四辺の前後合成
概要：三正方形の四つの合成面を、元の前後の復号辺の前後合成として厳密に回収する。
方針：同じ共有面から最初・最後の水平射を照合し、元の三角形の指定面を使う。
規約：元の全区間と水平射を保存し、Kan の充填を選び直さない。
使われ方：二本の適合区間と合成射の適合区間の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.CoherentPathCoordinates SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kCompositionPrismWhiskerFacesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 中央の三単体の最初の辺は、元の前の射の suspension。 -/
lemma kKanOriginalCompositionImage_first_middle :
    (SimplicialNerve PointedSimplicialSet.{u}).map tetrahedronFirstEdgeMap.op
      (kKanOriginalCompositionImage r F f g 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)).edge :=
  (tetrahedronFirstEdge_of_face (kKanOriginalCompositionImage_first_lower r F f g)).trans
    (kKanSuspensionMappingTriangles r F f).bottomRight.d₂

/-- 中央の三単体の最後の辺は、元の後続射の次段。 -/
lemma kKanOriginalCompositionImage_last_middle :
    (SimplicialNerve PointedSimplicialSet.{u}).map tetrahedronLastEdgeMap.op
      (kKanOriginalCompositionImage r F f g 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kKanSequenceLevelMap (F.map g) (r + 1))).edge :=
  (tetrahedronLastEdge_of_face (kKanOriginalCompositionImage_second_upper r F f g)).trans
    (kKanSuspensionMappingTriangles r F g).leftTop.d₀

/-- 共有面の同じ端の辺は、元の同じ水平射を保持する。 -/
lemma kKanOriginalCompositionImage_first_last :
    (SimplicialNerve PointedSimplicialSet.{u}).map tetrahedronFirstEdgeMap.op
      (kKanOriginalCompositionImage r F f g 2) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)).edge := by
  have hs : ((Δ[2] : SSet.{u + 1}) ⊗ Δ[1]).map tetrahedronFirstEdgeMap.op
      (trianglePrismTetrahedron 2) =
      ((Δ[2] : SSet.{u + 1}) ⊗ Δ[1]).map tetrahedronFirstEdgeMap.op
        (trianglePrismTetrahedron 1) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl
  have hq := NatTrans.naturality_apply (kKanOriginalCompositionPrism r F f g)
    tetrahedronFirstEdgeMap.op (trianglePrismTetrahedron 2)
  have hm := NatTrans.naturality_apply (kKanOriginalCompositionPrism r F f g)
    tetrahedronFirstEdgeMap.op (trianglePrismTetrahedron 1)
  exact (hq.symm.trans
    ((congrArg ((kKanOriginalCompositionPrism r F f g).app _) hs).trans hm)).trans
    (kKanOriginalCompositionImage_first_middle r F f g)

/-- 共有面の同じ端の辺は、元の同じ水平射を保持する。 -/
lemma kKanOriginalCompositionImage_last_first :
    (SimplicialNerve PointedSimplicialSet.{u}).map tetrahedronLastEdgeMap.op
      (kKanOriginalCompositionImage r F f g 0) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kKanSequenceLevelMap (F.map g) (r + 1))).edge := by
  have hs : ((Δ[2] : SSet.{u + 1}) ⊗ Δ[1]).map tetrahedronLastEdgeMap.op
      (trianglePrismTetrahedron 0) =
      ((Δ[2] : SSet.{u + 1}) ⊗ Δ[1]).map tetrahedronLastEdgeMap.op
        (trianglePrismTetrahedron 1) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl
  have hq := NatTrans.naturality_apply (kKanOriginalCompositionPrism r F f g)
    tetrahedronLastEdgeMap.op (trianglePrismTetrahedron 0)
  have hm := NatTrans.naturality_apply (kKanOriginalCompositionPrism r F f g)
    tetrahedronLastEdgeMap.op (trianglePrismTetrahedron 1)
  exact (hq.symm.trans
    ((congrArg ((kKanOriginalCompositionPrism r F f g).app _) hs).trans hm)).trans
    (kKanOriginalCompositionImage_last_middle r F f g)

/-- 元の合成面の指定辺は、同じ入力射の復号区間の通常の前後合成。 -/
lemma kKanOriginalCompositionMappingSquare_first_upper_post :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      kKanOriginalCompositionMappingSquare r F f g 0 =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f)).edge ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right := by
  have h := tetrahedronTrace_include_second_specified _ _ _
    (kKanSequenceLevelMap (F.map g) (r + 1)) (kKanSuspensionMappingTriangles r F f).leftTop
    (kKanOriginalCompositionImage r F f g 0)
    (kKanOriginalCompositionImage_first_upper r F f g)
    (kKanOriginalCompositionImage_last_first r F f g)
    ((trianglePrismImage_hom (kKanOriginalCompositionPrism r F f g) 0).trans
      (kKanOriginalCompositionPrism_hom r F f g))
  simpa only [kKanOriginalCompositionMappingSquare, trianglePrismMappingSquare, Category.assoc,
    eqToHom_trans, kKanOriginalCompositionImage, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension, PointedEnrichment.hom_eq,
    PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq,
    coherentSquareMappingLeftTop] using h

/-- 元の合成面の指定辺は、同じ入力射の復号区間の通常の前後合成。 -/
lemma kKanOriginalCompositionMappingSquare_first_lower_post :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      kKanOriginalCompositionMappingSquare r F f g 1 =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f)).edge ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right := by
  have h := tetrahedronTrace_include_second_specified _ _ _
    (kKanSequenceLevelMap (F.map g) (r + 1)) (kKanSuspensionMappingTriangles r F f).bottomRight
    (kKanOriginalCompositionImage r F f g 1)
    (kKanOriginalCompositionImage_first_lower r F f g)
    (kKanOriginalCompositionImage_last_middle r F f g)
    ((trianglePrismImage_hom (kKanOriginalCompositionPrism r F f g) 1).trans
      (kKanOriginalCompositionPrism_hom r F f g))
  simpa only [kKanOriginalCompositionMappingSquare, trianglePrismMappingSquare, Category.assoc,
    eqToHom_trans, kKanOriginalCompositionImage, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension, PointedEnrichment.hom_eq,
    PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq,
    coherentSquareMappingBottomRight] using h

/-- 元の合成面の指定辺は、同じ入力射の復号区間の通常の前後合成。 -/
lemma kKanOriginalCompositionMappingSquare_second_upper_pre :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      kKanOriginalCompositionMappingSquare r F f g 1 =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F g)).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  have h := tetrahedronTrace_include_first_specified
    (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r) _ _ _
    (kKanSuspensionMappingTriangles r F g).leftTop (kKanOriginalCompositionImage r F f g 1)
    (kKanOriginalCompositionImage_first_middle r F f g)
    (kKanOriginalCompositionImage_second_upper r F f g)
    ((trianglePrismImage_hom (kKanOriginalCompositionPrism r F f g) 1).trans
      (kKanOriginalCompositionPrism_hom r F f g))
  simpa only [kKanOriginalCompositionMappingSquare, trianglePrismMappingSquare, Category.assoc,
    eqToHom_trans, kKanOriginalCompositionImage, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension, PointedEnrichment.hom_eq,
    PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq,
    coherentSquareMappingLeftTop] using h

/-- 元の合成面の指定辺は、同じ入力射の復号区間の通常の前後合成。 -/
lemma kKanOriginalCompositionMappingSquare_second_lower_pre :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      kKanOriginalCompositionMappingSquare r F f g 2 =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F g)).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  have h := tetrahedronTrace_include_first_specified
    (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r) _ _ _
    (kKanSuspensionMappingTriangles r F g).bottomRight (kKanOriginalCompositionImage r F f g 2)
    (kKanOriginalCompositionImage_first_last r F f g)
    (kKanOriginalCompositionImage_second_lower r F f g)
    ((trianglePrismImage_hom (kKanOriginalCompositionPrism r F f g) 2).trans
      (kKanOriginalCompositionPrism_hom r F f g))
  simpa only [kKanOriginalCompositionMappingSquare, trianglePrismMappingSquare, Category.assoc,
    eqToHom_trans, kKanOriginalCompositionImage, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension, PointedEnrichment.hom_eq,
    PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq,
    coherentSquareMappingBottomRight] using h

end SerrePositivity.KST.SConstruction

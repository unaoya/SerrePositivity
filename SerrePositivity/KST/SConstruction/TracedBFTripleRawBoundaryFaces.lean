module
public import SerrePositivity.KST.SConstruction.TracedBFTripleRawBoundary

/-! # 第四辺 raw 比較問題の元の全円柱と全三角形面
概要：比較すべき二 raw 辺を、元の全 raw 合成円柱と元の第二全三角形の面として回収する。
方針：指定 BF 境界と全 raw 円柱の厳密な射影式、元の第二三角形の下面の式を使う。
規約：元の実射全体の等号を保存する。raw 高次比較の存在はまだ結論しない。
使われ方：高次 raw prism の両端を既存の第四辺問題へ厳密に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance tracedTripleRawFacesSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})

/-- 元の BF 合成境界円柱の全射影は、同じ直通列点における元の全 raw 円柱。 -/
lemma monicKPrismTracedBFCompositionBoundary_projection {x y z : I} (f : x ⟶ y) (g : y ⟶ z) :
    (monicKPrismTracedBFCompositionBoundary F f g).h ≫
        kRawMappingProjection (F.obj x) (F.obj z) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeRawComparison F f g).h := by
  rw [← monicKPrismNativeBFComparisonData_composition_boundary, Category.assoc,
    monicKPrismNativeBFComparisonData_projection]

variable {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 指定左辺の全 raw 射影は、元の左合成 raw 円柱の元の直通列制限そのもの。 -/
lemma monicKTracedNativeTriplePrescribedEdge_raw :
    SSet.yonedaEquiv.symm
        ((monicKTracedNativeTriplePrescribedEdge F f g h).map
          (kRawMappingProjection (F.obj w) (F.obj z))).edge =
      lift (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect (f ≫ g) h) ▷ (Δ[1] : SSet.{u})) ≫
          (monicKPrismNativeRawComparison F (f ≫ g) h).h := by
  rw [SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp, monicKTracedNativeTriplePrescribedEdge_edge,
    monicKTracedSpectrumCompositionEdge_map, Category.assoc,
    monicKPrismTracedBFCompositionBoundary_projection]

/-- 生成第四辺の全 raw 射影は、元の第二全三角形の同じ下面の射影そのもの。 -/
lemma monicKTracedCoherentTripleGeneratedEdge_raw :
    SSet.yonedaEquiv.symm
        ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
          (kRawMappingProjection (F.obj w) (F.obj z))).edge =
      stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm
        (monicKTracedCoherentTripleCompositionDiamond F f g h).second.simplex ≫
          kRawMappingProjection (F.obj w) (F.obj z) := by
  rw [SSet.Edge.map_edge]
  exact (SSet.yonedaEquiv_symm_comp
    (monicKTracedCoherentTripleGeneratedEdge F f g h).edge
    (kRawMappingProjection (F.obj w) (F.obj z))).symm.trans
      (congrArg (fun k => k ≫ kRawMappingProjection (F.obj w) (F.obj z))
        (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm
          (monicKTracedCoherentTripleCompositionDiamond F f g h).second).symm)

end SerrePositivity.KST.SConstruction

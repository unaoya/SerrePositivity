module
public import SerrePositivity.KST.SConstruction.TracedBFTripleRawBoundaryFaces

/-! # 元の BF 合成比較の零段は元の同じ定数辺
概要：元の BF 合成比較の全 raw 零段と、同じ BF 零段の定数性を厳密に回収する。
方針：元の raw 円柱の零段固定式を直通列点へ制限し、零段を保つ置換射影を使う。
規約：全一単体の実射の等号を保存し、成分の一致だけには弱めない。
使われ方：第四辺 raw 比較の零段で、指定側と三つの既存 BF 辺を定数辺へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories Spectra.PointedMapping
open scoped Simplicial
local instance tracedCompositionZeroSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の raw 射影の零段評価は、零段を保つ同じ BF 評価そのもの。 -/
lemma kRawMappingProjection_zero (X Y : StableModel.{u}) :
    kRawMappingProjection X Y ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum X) (kKanSequence Y) 0 =
      OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) 0 := by
  rw [kRawMappingProjection_evaluation]
  change _ ≫ (PointedObject.basedHomMap ((kOmegaSpectrum X).level 0).space
    (𝟙 (boundaryKSpaceFunctor.obj Y))).right = _
  have hi := (PointedObject.basedHomFunctor ((kOmegaSpectrum X).level 0).space).map_id
    (boundaryKSpaceFunctor.obj Y)
  change PointedObject.basedHomMap _ (𝟙 _) = _ at hi
  rw [hi]
  exact Category.comp_id _

variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y z : I}
  (f : x ⟶ y) (g : y ⟶ z)

/-- 元の BF 比較辺の全 raw 零段は、元の合成射の同じ定数区間。 -/
lemma monicKTracedSpectrumCompositionEdge_raw_zero :
    SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        kRawMappingProjection (F.obj x) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) 0 =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) := by
  rw [monicKTracedSpectrumCompositionEdge_map, Category.assoc,
    ← Category.assoc (monicKPrismTracedBFCompositionBoundary F f g).h,
    monicKPrismTracedBFCompositionBoundary_projection, Category.assoc,
    monicKPrismNativeRawComparison_zero]
  simp only [SSet.comp_const]

/-- 零段を保つ置換のため、元の BF 比較辺自身の全零段も同じ定数区間。 -/
lemma monicKTracedSpectrumCompositionEdge_zero :
    SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj z)) 0 =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) := by
  rw [← kRawMappingProjection_zero]
  exact monicKTracedSpectrumCompositionEdge_raw_zero F f g

end SerrePositivity.KST.SConstruction

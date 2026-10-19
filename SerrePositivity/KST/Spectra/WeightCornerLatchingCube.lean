module

public import SerrePositivity.KST.Spectra.WeightCornerComparison

/-!
概要：corner の実際の相対 latching 射と立方体の表示の arrow 同型。
方針：latching と評価の二つの pushout 同型を相対 pushout へ送り、包含の後で比較射を照合する。
規約：選択した pushout の向きの違いは標準の対称同型で明示する。
使われ方：Goerss–Jardine VII §4。Reedy anodyne な重みと境界の相対 tensor の左側の同定。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.WeightCornerPushout
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F G : CosimplicialObject SSet.{u}} (θ : F ⟶ G)
  {A B : SSet.{u}} (i : A ⟶ B) (j : SimplexCategory)

/-- 実際の相対 latching の source から立方体の反対向きの pushout への比較。 -/
abbrev relativeCubeSourceMap :=
  pushout.map ((latchingEvaluation simplex j).map (corner θ i).ι)
    ((latchingComparison simplex j).app (corner θ i).pt)
    (cubeDiagonal θ i j) (cubeUpper θ i j)
    (WeightTensorLatching.iso G B j).hom (evaluationIso θ i j).hom (latchingIso θ i j).hom
    (latching_corner_map θ i j) (latching_comparison θ i j)

instance relativeCubeSourceMap_isIso : IsIso (relativeCubeSourceMap θ i j) :=
  pushout.map_isIso _ _ _ _ (WeightTensorLatching.iso G B j).hom
    (evaluationIso θ i j).hom (latchingIso θ i j).hom _ _

/-- corner の実際の相対 latching 射は立方体の latching 側の表示と同型。 -/
def relativeLatchingCubeArrowIso :
    Arrow.mk (relativeLatchingMap simplex j (corner θ i).ι) ≅
      Arrow.mk (RelativeWeightCornerCube.latchingFirst θ i j) := by
  let e := asIso (relativeCubeSourceMap θ i j) ≪≫
    pushoutSymmetry (cubeDiagonal θ i j) (cubeUpper θ i j)
  refine Arrow.isoMk e (Iso.refl _) ?_
  change (relativeCubeSourceMap θ i j ≫
    (pushoutSymmetry (cubeDiagonal θ i j) (cubeUpper θ i j)).hom) ≫
    RelativeWeightCornerCube.latchingFirst θ i j = _ ≫ 𝟙 _
  rw [Category.comp_id]
  dsimp only [RelativeWeightCornerCube.latchingFirst, PushoutCube.rightDesc]
  apply pushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, pushout.inl_desc]
    simp only [Category.assoc]
    rw [inl_comp_pushoutSymmetry_hom_assoc, pushout.inr_desc,
      WeightTensorLatching.iso_comparison]
    exact (inl_relativeLatchingMap simplex j (corner θ i).ι).symm
  · rw [← Category.assoc, ← Category.assoc, pushout.inr_desc]
    simp only [Category.assoc]
    rw [inr_comp_pushoutSymmetry_hom_assoc, pushout.inl_desc,
      evaluation_corner_map]
    exact (inr_relativeLatchingMap simplex j (corner θ i).ι).symm

end
end SerrePositivity.KST.Spectra.WeightCornerPushout

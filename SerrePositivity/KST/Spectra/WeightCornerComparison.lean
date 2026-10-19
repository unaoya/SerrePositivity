module

public import SerrePositivity.KST.Spectra.WeightCornerPushout

/-!
概要：corner の latching と評価の pushout 同型は実際の比較射を立方体の射へ送る。
方針：保存された pushout の二包含で自然性と tensor の交換式を照合する。
規約：源の対象の同型だけでなく比較射自体との可換性を証明する。
使われ方：Goerss–Jardine VII §4。実際の相対 latching 射の立方体表示。
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

/-- 立方体の二つの平行な pushout の間の標準射。 -/
abbrev cubeUpper := PushoutCube.upperMap
  (RelativeWeightCornerCube.faceA (A := A) θ j) (RelativeWeightCornerCube.faceF (F := F) i j)

/-- 立方体の上側の pushout から L(G) ⊗ B への標準射。 -/
abbrev cubeDiagonal := PushoutCube.diagonalMap (RelativeWeightCornerCube.faceTop θ i j)

/-- 実際の latching 比較射は交換同型の後で立方体の上側の射になる。 -/
lemma latching_comparison : (latchingComparison simplex j).app (corner θ i).pt ≫
    (evaluationIso θ i j).hom = (latchingIso θ i j).hom ≫ cubeUpper θ i j := by
  apply ((corner θ i).isPushout.map (latchingEvaluation simplex j)).hom_ext
  · rw [← Category.assoc, (latchingComparison simplex j).naturality, Category.assoc]
    erw [evaluationIso_inl θ i j, latchingIso_inl_assoc θ i j]
    change (latchingComparison simplex j).app (WeightTensorLatching.diagram G A) ≫ _ =
      (WeightTensorLatching.iso G A j).hom ≫ (pushout.inl _ _ ≫ cubeUpper θ i j)
    rw [pushout.inl_desc, ← Category.assoc, WeightTensorLatching.iso_comparison]
  · rw [← Category.assoc, (latchingComparison simplex j).naturality, Category.assoc]
    erw [evaluationIso_inr θ i j, latchingIso_inr_assoc θ i j]
    change (latchingComparison simplex j).app (WeightTensorLatching.diagram F B) ≫ _ =
      (WeightTensorLatching.iso F B j).hom ≫ (pushout.inr _ _ ≫ cubeUpper θ i j)
    rw [pushout.inr_desc, ← Category.assoc, WeightTensorLatching.iso_comparison]

/-- latching 上の corner の構造射は立方体の対角射になる。 -/
lemma latching_corner_map : (latchingEvaluation simplex j).map (corner θ i).ι ≫
    (WeightTensorLatching.iso G B j).hom =
      (latchingIso θ i j).hom ≫ cubeDiagonal θ i j := by
  apply ((corner θ i).isPushout.map (latchingEvaluation simplex j)).hom_ext
  · rw [← Category.assoc, ← Functor.map_comp, Functor.PushoutObjObj.inl_ι]
    erw [latchingIso_inl_assoc θ i j, pushout.inl_desc]
    exact WeightTensorLatching.iso_natural G i j
  · rw [← Category.assoc, ← Functor.map_comp, Functor.PushoutObjObj.inr_ι]
    erw [latchingIso_inr_assoc θ i j, pushout.inr_desc]
    exact WeightTensorLatching.iso_weight_natural θ B j

/-- 評価上の corner の構造射は二つの tensor 射から作る pushout の比較射。 -/
lemma evaluation_corner_map : (evaluationIso θ i j).hom ≫
    pushout.desc (G.obj j ◁ i) (θ.app j ▷ B) (whisker_exchange (θ.app j) i).symm =
      (corner θ i).ι.app j := by
  apply ((corner θ i).isPushout.map ((evaluation SimplexCategory SSet.{u}).obj j)).hom_ext
  · rw [← Category.assoc]
    erw [evaluationIso_inl θ i j, pushout.inl_desc]
    exact (NatTrans.congr_app (corner θ i).inl_ι j).symm
  · rw [← Category.assoc]
    erw [evaluationIso_inr θ i j, pushout.inr_desc]
    exact (NatTrans.congr_app (corner θ i).inr_ι j).symm

end
end SerrePositivity.KST.Spectra.WeightCornerPushout

module

public import SerrePositivity.KST.Spectra.WeightCornerLatchingCube

/-!
概要：立方体の中央二面を相対 latching の source の tensor と同定する。
方針：tensor の pushout 保存と左右の対称同型を合成し、各包含とパラメーターの射に照合する。
規約：source の同型と相対 latching の比較射の可換性をともに保持する。
使われ方：Goerss–Jardine VII §4。corner の product 側の表示への接続。
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

/-- 相対 latching の実際の source。 -/
abbrev relativeSource :=
  pushout ((latchingEvaluation simplex j).map θ) ((latchingComparison simplex j).app F)

/-- 立方体の中央面を相対 latching の source の tensor と同定する。 -/
def sourceTensorIso (A : SSet.{u}) :
    pushout ((latchingComparison simplex j).app F ▷ A)
      ((latchingEvaluation simplex j).map θ ▷ A) ≅ relativeSource θ j ⊗ A :=
  pushoutSymmetry _ _ ≪≫ PreservesPushout.iso (tensorRight A)
    ((latchingEvaluation simplex j).map θ) ((latchingComparison simplex j).app F)

@[reassoc]
lemma sourceTensorIso_inl (A : SSet.{u}) :
    pushout.inl _ _ ≫ (sourceTensorIso θ j A).hom =
      (pushout.inr ((latchingEvaluation simplex j).map θ)
        ((latchingComparison simplex j).app F) ▷ A) := by
  change pushout.inl _ _ ≫ ((pushoutSymmetry _ _).hom ≫ _) = _
  rw [← Category.assoc, inl_comp_pushoutSymmetry_hom]
  exact PreservesPushout.inr_iso_hom (tensorRight A)
    ((latchingEvaluation simplex j).map θ) ((latchingComparison simplex j).app F)

@[reassoc]
lemma sourceTensorIso_inr (A : SSet.{u}) :
    pushout.inr _ _ ≫ (sourceTensorIso θ j A).hom =
      (pushout.inl ((latchingEvaluation simplex j).map θ)
        ((latchingComparison simplex j).app F) ▷ A) := by
  change pushout.inr _ _ ≫ ((pushoutSymmetry _ _).hom ≫ _) = _
  rw [← Category.assoc, inr_comp_pushoutSymmetry_hom]
  exact PreservesPushout.inl_iso_hom (tensorRight A)
    ((latchingEvaluation simplex j).map θ) ((latchingComparison simplex j).app F)

/-- source の同型の後の相対 latching は立方体の中央面の比較射。 -/
lemma sourceTensorIso_comparison (A : SSet.{u}) :
    (sourceTensorIso θ j A).hom ≫ (relativeLatchingMap simplex j θ ▷ A) =
      PushoutCube.middleLeft (RelativeWeightCornerCube.faceA (A := A) θ j) := by
  apply pushout.hom_ext
  · rw [← Category.assoc, sourceTensorIso_inl, ← comp_whiskerRight, inr_relativeLatchingMap]
    exact (pushout.inl_desc _ _ _).symm
  · rw [← Category.assoc, sourceTensorIso_inr, ← comp_whiskerRight, inl_relativeLatchingMap]
    exact (pushout.inr_desc _ _ _).symm

/-- source の tensor 同型は立方体のもう一方の中央射に自然。 -/
lemma sourceTensorIso_natural :
    PushoutCube.middleRight (RelativeWeightCornerCube.faceF (F := F) i j)
        (RelativeWeightCornerCube.faceTop θ i j) ≫ (sourceTensorIso θ j B).hom =
      (sourceTensorIso θ j A).hom ≫ (relativeSource θ j ◁ i) := by
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc, Category.assoc, sourceTensorIso_inl]
    erw [sourceTensorIso_inl_assoc θ j A]
    exact whisker_exchange (pushout.inr ((latchingEvaluation simplex j).map θ)
      ((latchingComparison simplex j).app F)) i
  · rw [← Category.assoc, pushout.inr_desc, Category.assoc, sourceTensorIso_inr]
    erw [sourceTensorIso_inr_assoc θ j A]
    exact whisker_exchange (pushout.inl ((latchingEvaluation simplex j).map θ)
      ((latchingComparison simplex j).app F)) i

end
end SerrePositivity.KST.Spectra.WeightCornerPushout

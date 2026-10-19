module

public import SerrePositivity.KST.Spectra.RelativeWeightCornerCube
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：実際の余単体 corner の評価と latching の pushout 表示。
方針：二つの余極限保存同型と tensor の交換同型を合成する。
規約：corner は図式の圏の実際の pushout-product として構成する。
使われ方：Goerss–Jardine VII §4。立方体表示と相対 latching 射の接続。
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

/-- 重みの射とパラメーターの射の、図式の圏の実際の pushout-product。 -/
abbrev corner : (curriedTensor (CosimplicialObject SSet.{u})).PushoutObjObj
    θ ((Functor.const SimplexCategory).map i) :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- 各段の corner は二つの tensor 射の通常の pushout。 -/
def evaluationIso : (corner θ i).pt.obj j ≅ pushout (θ.app j ▷ A) (F.obj j ◁ i) :=
  (PreservesPushout.iso ((evaluation SimplexCategory SSet.{u}).obj j)
    (Functor.whiskerRight θ (tensorRight A)) (WeightTensorLatching.map F i)).symm

/-- latching の二辺を tensor と交換した pushout の比較射。 -/
abbrev latchingPushoutMap :=
  pushout.map
    ((latchingEvaluation simplex j).map (Functor.whiskerRight θ (tensorRight A)))
    ((latchingEvaluation simplex j).map (WeightTensorLatching.map F i))
    ((latchingEvaluation simplex j).map θ ▷ A) ((latchingEvaluation simplex j).obj F ◁ i)
    (WeightTensorLatching.iso G A j).hom (WeightTensorLatching.iso F B j).hom
    (WeightTensorLatching.iso F A j).hom
    (WeightTensorLatching.iso_weight_natural θ A j) (WeightTensorLatching.iso_natural F i j)

instance latchingPushoutMap_isIso : IsIso (latchingPushoutMap θ i j) :=
  pushout.map_isIso _ _ _ _ (WeightTensorLatching.iso G A j).hom
    (WeightTensorLatching.iso F B j).hom (WeightTensorLatching.iso F A j).hom _ _

/-- corner の latching は latching の二つの tensor 射の pushout。 -/
def latchingIso : (latchingEvaluation simplex j).obj (corner θ i).pt ≅
    pushout ((latchingEvaluation simplex j).map θ ▷ A) ((latchingEvaluation simplex j).obj F ◁ i) :=
  (PreservesPushout.iso (latchingEvaluation simplex j)
    (Functor.whiskerRight θ (tensorRight A)) (WeightTensorLatching.map F i)).symm ≪≫
      asIso (latchingPushoutMap θ i j)

/-- 評価の交換同型は corner の第一包含を保つ。 -/
@[reassoc]
lemma evaluationIso_inl : (corner θ i).inl.app j ≫ (evaluationIso θ i j).hom =
    pushout.inl (θ.app j ▷ A) (F.obj j ◁ i) := by
  exact PreservesPushout.inl_iso_inv ((evaluation SimplexCategory SSet.{u}).obj j)
    (Functor.whiskerRight θ (tensorRight A)) (WeightTensorLatching.map F i)

/-- 評価の交換同型は第二包含も保つ。 -/
@[reassoc]
lemma evaluationIso_inr : (corner θ i).inr.app j ≫ (evaluationIso θ i j).hom =
    pushout.inr (θ.app j ▷ A) (F.obj j ◁ i) := by
  exact PreservesPushout.inr_iso_inv ((evaluation SimplexCategory SSet.{u}).obj j)
    (Functor.whiskerRight θ (tensorRight A)) (WeightTensorLatching.map F i)

/-- latching の交換同型の第一包含での計算。 -/
@[reassoc]
lemma latchingIso_inl : (latchingEvaluation simplex j).map (corner θ i).inl ≫
    (latchingIso θ i j).hom = (WeightTensorLatching.iso G A j).hom ≫
      pushout.inl ((latchingEvaluation simplex j).map θ ▷ A)
        ((latchingEvaluation simplex j).obj F ◁ i) := by
  change (latchingEvaluation simplex j).map (pushout.inl _ _) ≫
    ((PreservesPushout.iso (latchingEvaluation simplex j)
      (Functor.whiskerRight θ (tensorRight A)) (WeightTensorLatching.map F i)).inv ≫ _) = _
  rw [← Category.assoc, PreservesPushout.inl_iso_inv]
  exact pushout.inl_desc _ _ _

/-- latching の交換同型の第二包含での計算。 -/
@[reassoc]
lemma latchingIso_inr : (latchingEvaluation simplex j).map (corner θ i).inr ≫
    (latchingIso θ i j).hom = (WeightTensorLatching.iso F B j).hom ≫
      pushout.inr ((latchingEvaluation simplex j).map θ ▷ A)
        ((latchingEvaluation simplex j).obj F ◁ i) := by
  change (latchingEvaluation simplex j).map (pushout.inr _ _) ≫
    ((PreservesPushout.iso (latchingEvaluation simplex j)
      (Functor.whiskerRight θ (tensorRight A)) (WeightTensorLatching.map F i)).inv ≫ _) = _
  rw [← Category.assoc, PreservesPushout.inr_iso_inv]
  exact pushout.inr_desc _ _ _

end
end SerrePositivity.KST.Spectra.WeightCornerPushout

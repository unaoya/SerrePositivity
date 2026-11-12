module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEvaluationWeak
public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineLocalizationHom
public import SerrePositivity.EInfinity.Hammock.AllMarkedLocalizationValueComparison
public import SerrePositivity.EInfinity.Hammock.HammockValueForward

/-!
# 元の全因子列の評価と同じ局所化評価の一致

概要：全因子列を自由 groupoid の値へ評価して局所化 Hom に戻すと元の評価に一致する。
方針：元の nil/cons 表示で帰納し、同じ三因子の合成則と指定因子の評価を使う。
規約：元の全 hammock・全標準射・通常の局所化 Q を保持する。
使われ方：元の自由圏の局所化評価自身の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma glue_localizationValue {X : Paths C} (t : MarkedSpine W Y n X) :
    (localizationValue W.paths X Y).app n (glue t) =
      letI := valueCategory W
      (valueToLocalization W).map (evaluatePoint t) := by
  let := valueCategory W
  induction t with
  | nil X p =>
    exact congrArg (fun k => k.app n p) (nativeValue_localizationValue W X Y)
  | cons X g p t ih =>
    have hp : (Zigzag.Value.colimitValue W.paths.Q W.paths.Q_inverts X g.val.left).app n
        ((AllMarked.inclusion W X g.val.left).app n p) =
        (markedValueDescent W W.paths.Q W.paths.Q_inverts).map
          ((AllMarked.nativeValue W X g.val.left).app n p) :=
      congrArg (fun k => k.app n p) (nativeValue_localizationValue W X g.val.left)
    change (Zigzag.Value.colimitValue W.paths.Q W.paths.Q_inverts X Y).app n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.right Y
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.left g.val.right
          ((AllMarked.inclusion W X g.val.left).app n p)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths g.val.hom.toPath n)) (glue t)) = _
    rw [Zigzag.Value.colimitValue_composePoint, Zigzag.Value.colimitValue_composePoint,
      Zigzag.Value.colimitValue_arrowPoint, hp]
    change (_ ≫ _) ≫ (localizationValue W.paths g.val.right Y).app n (glue t) = _
    rw [ih]
    exact Category.assoc _ _ _

lemma hammockEvaluation_localizationValue (X : Paths C) :
    hammockEvaluation W Y X ≫ (valueLocalizationHomIso W X Y).hom =
      localizationValue W.paths X Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨t, rfl⟩ := gluing_surjective W Y X n x
  change (valueLocalizationHomIso W X Y).hom.app n
    (evaluatePoint (markedSpine W Y n X (glue t))) = _
  rw [markedSpine_glue]
  exact (glue_localizationValue W Y t).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

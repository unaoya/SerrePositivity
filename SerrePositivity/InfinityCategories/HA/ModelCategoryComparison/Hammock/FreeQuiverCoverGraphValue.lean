module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiberGraph
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledColimit
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HammockValue

/-!
# 元の自由 groupoid の値による全 hammock の評価

概要：元の全語の graph の先頭行の値を単体的な評価として束ねる。
方針：全縦射の値の一致と元の全語の値の不変性を使う。
規約：宇宙を一般に保ち、同じ宇宙では既存の元の評価を回収する。
使われ方：元の hammock 上の値の fiber。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)

def graphValue (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y) where
  app _ := ↾fun τ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top (τ.obj 0)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_eq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top
      (τ.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))).symm

lemma graphValue_wordAction {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y).map f ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y b = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y a := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_value _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top f (τ.obj 0)

def graphValueLabels : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.Labels
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y)
    ((Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y) where
  value := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y
  naturality f := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue_wordAction A Y f

def hammockValue : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.colimitValue (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValueLabels A Y)

lemma graphInclusion_hammockValue (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y w ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.hammockValue A Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.ι_colimitValue (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValueLabels A Y) w

lemma hammockValue_eq_colimitValue {Q' : Type u} [Quiver.{u} Q'] (A' : Q') (Y' : Paths Q') :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.hammockValue A' Y' = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top ((Paths.of Q').obj A') Y' := by
  apply colimit.hom_ext
  intro w
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (⊤ : MorphismProperty (Paths Q')) ((Paths.of Q').obj A') Y' w ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.hammockValue A' Y' = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion _ _ _ w ≫ _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphInclusion_hammockValue, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.graphInclusion_colimitValue]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover

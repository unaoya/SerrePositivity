module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverFiberGraph
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SimplicialLabelledColimit
public import SerrePositivity.EInfinity.Hammock.HammockValue

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
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory CategoryTheory.Limits

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)

def graphValue (w : Word) : graph (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y) where
  app _ := ↾fun τ => Zigzag.Value.value positiveEvaluation positiveEvaluation_inverts_top (τ.obj 0)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    exact (Zigzag.Value.value_eq positiveEvaluation positiveEvaluation_inverts_top
      (τ.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))).symm

lemma graphValue_wordAction {a b : Word} (f : a ⟶ b) :
    (graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y).map f ≫
      graphValue A Y b = graphValue A Y a := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  exact Zigzag.Value.wordAction_value positiveEvaluation positiveEvaluation_inverts_top f (τ.obj 0)

def graphValueLabels : SimplicialLabelledColimit.Labels
    (graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y)
    ((Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y) where
  value := graphValue A Y
  naturality f := graphValue_wordAction A Y f

def hammockValue : colimitGraph (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y) :=
  SimplicialLabelledColimit.colimitValue (graphValueLabels A Y)

lemma graphInclusion_hammockValue (w : Word) :
    graphInclusion (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y w ≫
      hammockValue A Y = graphValue A Y w :=
  SimplicialLabelledColimit.ι_colimitValue (graphValueLabels A Y) w

lemma hammockValue_eq_colimitValue {Q' : Type u} [Quiver.{u} Q'] (A' : Q') (Y' : Paths Q') :
    hammockValue A' Y' = Zigzag.Value.colimitValue positiveEvaluation
      positiveEvaluation_inverts_top ((Paths.of Q').obj A') Y' := by
  apply colimit.hom_ext
  intro w
  change graphInclusion (⊤ : MorphismProperty (Paths Q')) ((Paths.of Q').obj A') Y' w ≫
    hammockValue A' Y' = graphInclusion _ _ _ w ≫ _
  rw [graphInclusion_hammockValue, Zigzag.Value.graphInclusion_colimitValue]
  rfl

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover

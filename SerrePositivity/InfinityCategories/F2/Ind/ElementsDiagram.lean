module

public import SerrePositivity.InfinityCategories.F1.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.PresheafPointwiseColimits

/-!
概要：前層の元の小さい right unstraightening を添字とする、表現可能前層の図式を固定する。
方針：元の射影を同じ Yoneda 関手へ合成し、各点余極限の存在を適用する。
規約：余極限の頂点が元の前層である密度定理は別工程。ここで仮定しない。
使われ方：F2N-2(a)、HTT 5.1.5.3 の生成図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 元の前層の小さい元の圏は、元の C 上の right fibration の全空間として quasicategory。 -/
instance presheafElements_quasicategory : Quasicategory (smallRightUnstraightening F) :=
  quasicategory_of_innerFibration (smallRightUnstraighteningProjection F)

/-- 元の前層の同じ小さい元の圏から、元の Yoneda 像への図式。 -/
def presheafElementsYonedaDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶ PresheafInfinity C :=
  (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F) ≫ yonedaInfinityMap C

/-- 生成図式の各対象は、同じ射影の像の元の表現可能前層そのもの。 -/
lemma presheafElementsYonedaDiagram_vertex (e : (smallRightUnstraightening F) _⦋0⦌) :
    (presheafElementsYonedaDiagram F).app (Opposite.op ⦋0⦌) (ULift.up e) =
      functorVertex (representablePresheafInfinity
        ((smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌) e)) := by
  change (yonedaInfinityMap C).app (Opposite.op ⦋0⦌)
    (ULift.up ((smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌) e)) = _
  exact yonedaInfinityMap_vertex _

/-- 同じ小さい生成図式は、全頂点で余極限となる native な全余錐を持つ。 -/
lemma presheafElementsYonedaDiagram_exists_colimitCone :
    ∃ c : JoinCocone (presheafElementsYonedaDiagram F), IsColimitCone c ∧
      ∀ x : C _⦋0⦌, IsColimitCone (mapJoinCocone (presheafInfinityEvaluation x) c) :=
  presheafInfinity_exists_colimitCone _

/-- 元の小さい元の圏による生成図式の、選択した同じ native な余極限余錐。 -/
def presheafElementsColimitCocone : JoinCocone (presheafElementsYonedaDiagram F) :=
  Classical.choose (presheafElementsYonedaDiagram_exists_colimitCone F)

/-- 選択した元の全余錐は余極限。元の前層との比較は密度定理の残り。 -/
lemma presheafElementsColimitCocone_isColimit :
    IsColimitCone (presheafElementsColimitCocone F) :=
  (Classical.choose_spec (presheafElementsYonedaDiagram_exists_colimitCone F)).1

/-- 選択した同じ余極限は、元の各評価で余極限となる。 -/
lemma presheafElementsColimitCocone_evaluation (x : C _⦋0⦌) :
    IsColimitCone
      (mapJoinCocone (presheafInfinityEvaluation x) (presheafElementsColimitCocone F)) :=
  (Classical.choose_spec (presheafElementsYonedaDiagram_exists_colimitCone F)).2 x

end SerrePositivity.InfinityCategories.F2.Ind

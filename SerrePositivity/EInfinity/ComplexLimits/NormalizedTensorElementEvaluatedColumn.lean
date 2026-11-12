module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveCoconePrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalCoconeSimplex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDiagram

/-!
概要：元の評価の通常余錐と全有限列の終端付き図式を作る。
方針：同じ実評価を Hom 持ち上げし、元の終端追加関手を使う。
規約：全対象・前面射・終端射を保つ。使われ方：大域評価三角形の通常部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementEvaluationCocone : Cocone (normalizedTensorElementDiagram A X Y) where
  pt := Y
  ι := normalizedTensorElementEvaluation A X Y

def normalizedTensorElementLiftedEvaluationCocone :
    Cocone (FrameHom.MixedNerve.lifted (normalizedTensorElementDiagram A X Y)) :=
  FrameHom.MixedNerve.liftedCocone (normalizedTensorElementEvaluationCocone A X Y)

def normalizedTensorElementEvaluatedColumn {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    ComposableArrows (Complex A) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram (normalizedTensorElementLiftedEvaluationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1}) ⋙ ULiftHom.down.{u, u + 1, u + 1}

lemma normalizedTensorElementEvaluatedColumn_obj_castSucc {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    (normalizedTensorElementEvaluatedColumn A X Y c).obj i.castSucc =
      (normalizedTensorElementDiagram A X Y).obj (c.obj i) := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (normalizedTensorElementLiftedEvaluationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1})).obj i.castSucc) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast]
  rfl

lemma normalizedTensorElementEvaluatedColumn_obj_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorElementEvaluatedColumn A X Y c).obj (Fin.last (n + 1)) = Y := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (normalizedTensorElementLiftedEvaluationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1})).obj (Fin.last (n + 1))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last]
  rfl


private lemma downMap_heq {C : Type (u + 1)} [Category.{u} C]
    {x y x' y' : ULiftHom.{u + 1} C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (hf : HEq f g) :
    HEq (ULiftHom.down.{u, u + 1, u + 1}.map f)
      (ULiftHom.down.{u, u + 1, u + 1}.map g) := by
  cases hx
  cases hy
  cases eq_of_heq hf
  rfl

lemma normalizedTensorElementEvaluatedColumn_map_cast_cast {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((normalizedTensorElementEvaluatedColumn A X Y c).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      ((normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hij))) := by
  let L := normalizedTensorElementLiftedEvaluationCocone A X Y
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_cast L Γ i j hij
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ j
  exact downMap_heq hx hy _ _ he

lemma normalizedTensorElementEvaluatedColumn_map_cast_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    HEq ((normalizedTensorElementEvaluatedColumn A X Y c).map
      (homOfLE (Fin.le_last i.castSucc)))
      ((normalizedTensorElementEvaluation A X Y).app (c.obj i)) := by
  let L := normalizedTensorElementLiftedEvaluationCocone A X Y
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_last L Γ i
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last L Γ
  exact downMap_heq hx hy _ _ he

end SerrePositivity.EInfinity.ComplexLimits

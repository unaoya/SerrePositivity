module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveCoconePrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalCoconeSimplex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementDiagram

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementEvaluationCocone : Cocone (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y) where
  pt := Y
  ι := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y

def normalizedTensorElementLiftedEvaluationCocone :
    Cocone (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.lifted (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedCocone (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationCocone A X Y)

def normalizedTensorElementEvaluatedColumn {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    ComposableArrows (Complex A) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedEvaluationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1}) ⋙ ULiftHom.down.{u, u + 1, u + 1}

lemma normalizedTensorElementEvaluatedColumn_obj_castSucc {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c).obj i.castSucc =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i) := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedEvaluationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1})).obj i.castSucc) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast]
  rfl

lemma normalizedTensorElementEvaluatedColumn_obj_last {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c).obj (Fin.last (n + 1)) = Y := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedEvaluationCocone A X Y)
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
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hij))) := by
  let L := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedEvaluationCocone A X Y
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_cast L Γ i j hij
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ j
  exact _root_.SerrePositivity.ComplexLimits.downMap_heq hx hy _ _ he

lemma normalizedTensorElementEvaluatedColumn_map_cast_last {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c).map
      (homOfLE (Fin.le_last i.castSucc)))
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj i)) := by
  let L := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedEvaluationCocone A X Y
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_last L Γ i
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last L Γ
  exact _root_.SerrePositivity.ComplexLimits.downMap_heq hx hy _ _ he

end SerrePositivity.ComplexLimits

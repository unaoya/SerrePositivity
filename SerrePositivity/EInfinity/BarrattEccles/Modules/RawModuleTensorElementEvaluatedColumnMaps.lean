module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementEvaluatedColumn

/-!
概要：終端付き実列の通常射と終端への射を、元の frame 射と 評価 自身へ戻す。
方針：既存の終端追加関手の全射を同じ Hom の上下写像で移す。
規約：HA Construction 1.3.1.13、対象の輸送を異種等号で保持する。使われ方：三相単体 の通常閉 cochain の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma downMap_heq {C : Type (u + 1)} [Category.{u} C]
    {x y x' y' : ULiftHom.{u + 1} C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (hf : HEq f g) :
    HEq (ULiftHom.down.{u, u + 1, u + 1}.map f)
      (ULiftHom.down.{u, u + 1, u + 1}.map g) := by
  cases hx
  cases hy
  cases eq_of_heq hf
  rfl

lemma strictRawModuleTensorElementEvaluatedColumn_map_cast_cast {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((strictRawModuleTensorElementEvaluatedColumn A X P Q c).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      ((strictRawModuleTensorElementDiagram A X P Q).map (c.map (homOfLE hij))) := by
  let L := strictRawModuleTensorElementEvaluationCocone A X P Q
  let Γ := c
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_cast L Γ i j hij
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ j
  exact downMap_heq hx hy _ _ he

lemma strictRawModuleTensorElementEvaluatedColumn_map_cast_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    HEq ((strictRawModuleTensorElementEvaluatedColumn A X P Q c).map
      (homOfLE (Fin.le_last i.castSucc)))
      ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj i)) := by
  let L := strictRawModuleTensorElementEvaluationCocone A X P Q
  let Γ := c
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_last L Γ i
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last L Γ
  exact downMap_heq hx hy _ _ he

end SerrePositivity.EInfinity.BarrattEccles

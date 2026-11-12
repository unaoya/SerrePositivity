module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceSquareCones

/-!
概要：一脚 Kan fibration の正方形が与える空間の native な極限錐。
方針：γ3 の全豊穣 Hom による cospan の極限判定へ接続する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC


variable {K E D B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (p : E ⟶ B) (q : D ⟶ B)
variable (a : K.obj ⟶ E.obj) (b : K.obj ⟶ D.obj)
variable (h : IsPullback a b (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q))
/-- 概要：一脚 Kan fibration の正方形が与える空間の native な極限錐。
方針：γ3 の全豊穣 Hom による cospan の極限判定へ接続する。
規約：正方形の元の頂点を引き戻し対象に選び直さない。
使われ方：Tamme Remark 6 のホモトピー引き戻しの証明。 -/
def spaceSquareCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram p q)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareOrdinaryCone p q a b h)).cast
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _)
/-- 概要：一脚 Kan fibration の正方形が与える空間の native な極限錐。
方針：γ3 の全豊穣 Hom による cospan の極限判定へ接続する。
規約：正方形の元の頂点を引き戻し対象に選び直さない。
使われ方：Tamme Remark 6 のホモトピー引き戻しの証明。 -/
lemma spaceSquareCone_isLimit [Fibration (show E.obj ⟶ B.obj from p)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spaceSquareCone p q a b h) := by
  have : ∀ X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram p q) X).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun X ↦ by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op X)).map p)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration X p
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareOrdinaryCone p q a b h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareOrdinaryCone_forget_isLimit p q a b h))
/-- 概要：一脚 Kan fibration の正方形が与える空間の native な極限錐。
方針：γ3 の全豊穣 Hom による cospan の極限判定へ接続する。
規約：正方形の元の頂点を引き戻し対象に選び直さない。
使われ方：Tamme Remark 6 のホモトピー引き戻しの証明。 -/
lemma spaceSquareCone_vertex :
    (spaceSquareCone p q a b h).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex K := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

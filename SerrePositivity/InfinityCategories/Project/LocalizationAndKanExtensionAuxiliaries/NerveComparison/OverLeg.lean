module

public import SerrePositivity.InfinityCategories.HTT.Section1_2_9.OverIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeLegReverse
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceDiagramConeMap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderCanonicalCone
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OppositeVertices

/-!
概要：Over の nerve と native な slice の比較が構造射を保つことを証明する。
方針：反対 Under の余錐の脚を反転し標的を元へ戻す。
規約：元の指定対象・構造射を保持する。
使われ方：B5 の指定単位の左 Kan 局所余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C : Type u} [Category.{u} C] (c : C)


/-- 概要：Over の頂点の中間表示は反対の Under の余錐の反転。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma nerveOverRawSliceIso_vertex (x : Over c) :
    (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderSimplex (op c)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk x.hom.op))) := by
  rfl

/-- 概要：Over の頂点を表す錐の元の射を反転と前後合成で表示する。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma nerveOverIso_vertex_val (x : Over c) :
    ((_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderSimplex (op c)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk x.hom.op)))).val ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso, Iso.trans_hom, asIso_hom]
  simp only [NatTrans.comp_app_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_cast_val]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).val ≫ _ = _
  rw [nerveOverRawSliceIso_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverBase_eq c

/-- 概要：Over の頂点を表す錐の脚は元の構造射に一致する。
方針：Under の零単体の反転と混合辺の公式を使う。
規約：元の Over の対象と構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の同定。 -/
lemma nerveOverIso_leg (x : Over c) :
    ((_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).val.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) =
        ComposableArrows.mk₁ x.hom := by
  rw [nerveOverIso_vertex_val]
  change (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom.app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderSimplex (op c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk x.hom.op)))).val.app (Opposite.op ⦋1⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.opIso ⦋0⦌).inv).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinConeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinConeLegSimplex_natural]
  have hp : (stdSimplex.opIso.{u} ⦋0⦌).inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) =
        SSet.opObjEquiv.symm (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) := by
    apply SSet.opObjEquiv.injective
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_leg]
  have hu : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderSimplex (op c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk x.hom.op))).val.app
      (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) =
        ComposableArrows.mk₁ x.hom.op := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap (op c))).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex (Under.mk x.hom.op)) = _
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderUncurry_leg (op c) (Under.mk x.hom.op)
  rw [hu]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnopIso_edge x.hom

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpaceProducts
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SpacePointLimitDetection

/-!
概要：任意の小さい離散 coherent 空間値図式は、元の頂点の Kan 積から極限を持つ。
方針：離散 nerve からの図式は元の頂点で決まり、元の Kan 図式と厳密に一致する。
規約：底の族の有限性は不要。元の図式を置き換えず等式で移す。
使われ方：一点からの切断判定による有限積保存と P_Σ への Yoneda 因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 持ち上げた離散 nerve からの二つの図式は、元の全頂点で一致すれば等しい。 -/
lemma liftedDiscreteDiagram_ext {J : Type u} {X : SSet.{u + 1}}
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X}
    (h : ∀ j : Discrete J, F.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)) =
      G.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))) : F = G := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  let j := s.down.obj 0
  let α := SimplexCategory.const ⦋n⦌ ⦋0⦌ 0
  have hs : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J))).map α.op
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)) = s := by
    apply ULift.ext
    change ((Functor.const (Fin (n + 1))).obj j) = s.down
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    exact IsDiscrete.eq_of_hom (s.down.map (homOfLE (Fin.zero_le i)))
  let v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J))) _⦋0⦌ :=
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)
  have hf := ConcreteCategory.congr_hom (F.naturality α.op) v
  have hg := ConcreteCategory.congr_hom (G.naturality α.op) v
  calc
    _ = X.map α.op (F.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))) := by
      simpa only [ConcreteCategory.comp_apply, v, hs] using hf
    _ = X.map α.op (G.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))) :=
      congrArg (X.map α.op) (h j)
    _ = _ := by simpa only [ConcreteCategory.comp_apply, v, hs] using hg.symm

/-- 元の離散 coherent 空間値図式の、元の頂点の Kan 対象の族。 -/
def discreteCoherentKanDiagram {J : Type u}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  Discrete.functor (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject
    (F.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))))

/-- 元の離散図式は、元の頂点の Kan 族の coherent 表示そのもの。 -/
lemma discreteCoherentKanDiagram_eq {J : Type u}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (discreteCoherentKanDiagram F) = F := by
  apply liftedDiscreteDiagram_ext
  intro j
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertexEquiv.apply_symm_apply _

/-- 任意の元の小さい離散 coherent 空間値図式は、元の Kan 積錐から極限を持つ。 -/
lemma hasLimit_discreteCoherentSpaceDiagram {J : Type u}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F := by
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spaceProductCone (discreteCoherentKanDiagram F)).cast
    (discreteCoherentKanDiagram_eq F), ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spaceProductCone_isLimitCone _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

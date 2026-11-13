module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexSquarePostcomposeJoin
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberCofiberComparisonProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CosliceSquareDiagram

/-! # 四角形の後合成の coslice 辺

概要：span を固定した後合成比較を coslice の実際の辺へ移す。
方針：join を curry し、終点射影を比較三単体の最後の辺で計算する。
規約：余極限性は仮定しない。使われ方：D7 の suspension の比較射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C D E : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C D) (q : D ⟶ E)

/-- 後合成比較の join 写像は元の span を固定する。 -/
lemma postcomposeJoin_fixed :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (SSet.horn 2 0 : SSet.{u + 1}) Δ[1] ≫ s.postcomposeJoin q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (SSet.horn 2 0 : SSet.{u + 1}) Δ[0] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ (1 : Fin 2))) ≫
        s.postcomposeJoin q := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeJoin.postcomposeJoin_face_one]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square).property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge (postcomposeJoin_fixed)


/-- 後合成した四角形を元の span の上の余錐として読む。 -/
def postcomposeCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (s.postcompose q).square).val, by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeJoin.postcomposeJoin_face_zero, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
    exact s.postcomposeJoin_fixed q⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge (postcomposeCocone)


/-- 四角形の後合成を表す実際の coslice 辺。 -/
def postcomposeSliceEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square) (s.postcomposeCocone q) where
  edge := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (s.postcomposeJoin q) (s.postcomposeJoin_fixed q))
  src_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceUnderCurry_vertex_of_join _ _ 1 _ (s.postcomposeJoin_face_one q)
  tgt_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceUnderCurry_vertex_of_join _ _ 0 _ (s.postcomposeJoin_face_zero q)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge (postcomposeSliceEdge)


/-- Join の右因子は後合成射 q。 -/
lemma postcomposeJoin_suffix :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (SSet.horn 2 0 : SSet.{u + 1}) Δ[1] ≫ s.postcomposeJoin q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge q).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_lastEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeJoin.postcomposeJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_lastEdge _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge (postcomposeJoin_suffix)


/-- Coslice の後合成比較辺の終点射影は q の辺。 -/
lemma postcomposeSliceEdge_projection :
    ((s.postcomposeSliceEdge q).map ((SSet.truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge q).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)).app _
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (s.postcomposeJoin q) (s.postcomposeJoin_fixed q))) = _
  rw [← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection, postcomposeJoin_suffix]
  exact SSet.yonedaEquiv.apply_symm_apply _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge (postcomposeSliceEdge_projection)


/-- Coslice 比較を四角形全体の関手単体集合の辺へ写す。 -/
def postcomposeSquareEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      ((ihom
        ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (s.postcompose q).square) := by
  let e := (s.postcomposeSliceEdge q).map ((SSet.truncation 2).map
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)))
  refine ⟨e.edge, e.src_eq.trans ?_, e.tgt_eq.trans ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_pushoutCocone s.square
  · change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square)).app (Opposite.op ⦋0⦌)
      (s.postcomposeCocone q) = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_vertex]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (s.postcompose q).square)) = _
    rw [Iso.inv_hom_id_assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge (postcomposeSquareEdge)


end SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge

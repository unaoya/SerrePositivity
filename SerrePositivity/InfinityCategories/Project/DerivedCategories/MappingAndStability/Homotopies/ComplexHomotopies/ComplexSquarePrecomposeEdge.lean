module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexSquarePrecomposeJoin
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagram

/-! # 四角形の前合成の slice 辺

概要：cospan を固定した前合成比較を実際の slice 辺と四角形全体の辺へ移す。
方針：join を curry し、始点射影を比較三単体の最初の辺で計算する。
規約：極限性は仮定しない。使われ方：D7 の suspension の比較射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {V A B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C D) (p : V ⟶ A)

/-- 前合成比較の join 写像は元の cospan を固定する。 -/
lemma precomposeJoin_fixed :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ≫ s.precomposeJoin p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (SSet.horn 2 2) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1}))) ≫
        s.precomposeJoin p := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precomposeJoin_face_zero]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone s.square).property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeJoin_fixed)


/-- 前合成した四角形を元の cospan の上の錐として読む。 -/
def precomposeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (s.precompose p).square).val, by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precomposeJoin_face_one, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    exact s.precomposeJoin_fixed p⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeCone)


/-- 四角形の前合成を表す実際の slice 辺。 -/
def precomposeSliceEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square)))
      (s.precomposeCone p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone s.square) where
  edge := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (s.precomposeJoin p) (s.precomposeJoin_fixed p))
  src_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCurry_vertex_of_join _ _ 1 _ (s.precomposeJoin_face_one p)
  tgt_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCurry_vertex_of_join _ _ 0 _ (s.precomposeJoin_face_zero p)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeSliceEdge)


/-- Join の左因子は前合成射 p。 -/
lemma precomposeJoin_prefix :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ≫ s.precomposeJoin p =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge p).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cospanJoinLeft_firstEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precomposeJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_firstEdge _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeJoin_prefix)


/-- Slice の前合成比較辺の始点射影は p の辺。 -/
lemma precomposeSliceEdge_projection :
    ((s.precomposeSliceEdge p).map ((SSet.truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square)))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge p).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square)).app _
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (s.precomposeJoin p) (s.precomposeJoin_fixed p))) = _
  rw [← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection, precomposeJoin_prefix]
  exact SSet.yonedaEquiv.apply_symm_apply _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeSliceEdge_projection)


/-- Slice 比較を四角形全体の関手単体集合の辺へ写す。 -/
def precomposeSquareEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (s.precompose p).square) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) := by
  let e := (s.precomposeSliceEdge p).map ((SSet.truncation 2).map
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square)))
  refine ⟨e.edge, e.src_eq.trans ?_, e.tgt_eq.trans ?_⟩
  · change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square)).app (Opposite.op ⦋0⦌)
      (s.precomposeCone p) = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ (s.precompose p).square)) = _
    rw [Iso.inv_hom_id_assoc]
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_pullbackCone s.square

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeSquareEdge)


end SerrePositivity.InfinityCategories.Project.DerivedCategories

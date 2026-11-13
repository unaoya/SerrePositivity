module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberCofiberComparisonTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanJoinFaces

/-! # 双対比較三単体の join への貼合せ

概要：上下の比較三単体を貼り、標準 cofiber 余錐と元の fiber 余錐を結ぶ。
方針：span の join の二セル表示を使い、共通面と両端を照合する。
規約：同じ span 上の余錐の間の比較。使われ方：D7 の coslice 辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 上下の比較三単体は span の join の共通面で一致する。 -/
lemma fiberCofiberComparisonCells_compatible (g : B ⟶ D) (h : C ⟶ D) :
    SSet.stdSimplex.δ (1 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonLower g h) :
          (Δ[3] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (1 : Fin 4) ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonUpper g h) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparison_common g h)

/-- Span の join 上の実際の比較写像。 -/
def fiberCofiberComparisonJoin (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{u + 1}) Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).desc
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonLower g h))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonUpper g h))
    (fiberCofiberComparisonCells_compatible g h)

/-- 左セルへの制限は下側比較三単体。 -/
lemma fiberCofiberComparisonJoin_left (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft 1 ≫ fiberCofiberComparisonJoin g h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonLower g h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).inl_desc _ _ _

/-- 右セルへの制限は上側比較三単体。 -/
lemma fiberCofiberComparisonJoin_right (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight 1 ≫ fiberCofiberComparisonJoin g h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonUpper g h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).inr_desc _ _ _

/-- 比較写像の始点は標準 cofiber 余錐。 -/
lemma fiberCofiberComparisonJoin_face_one (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      fiberCofiberComparisonJoin g h =
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, Category.assoc,
      fiberCofiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonLower g h).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonLower_face_three]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare _ _)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, Category.assoc,
      fiberCofiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonUpper g h).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonUpper_face_three]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare _ _)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_upper]

/-- 比較写像の終点は元の標準 fiber 四角形の余錐。 -/
lemma fiberCofiberComparisonJoin_face_zero (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      fiberCofiberComparisonJoin g h = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, Category.assoc,
      fiberCofiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonLower g h).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonLower_face_two]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, Category.assoc,
      fiberCofiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonUpper g h).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonUpper_face_two]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_upper]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

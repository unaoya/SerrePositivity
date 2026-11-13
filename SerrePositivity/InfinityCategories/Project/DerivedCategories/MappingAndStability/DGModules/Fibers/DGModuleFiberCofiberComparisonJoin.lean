module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberComparisonTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanJoinFaces

/-! # 双対比較三単体の join への貼合せ

概要：上下の比較三単体を貼り、標準 cofiber 余錐と元の fiber 余錐を結ぶ。
方針：span の join の二セル表示を使い、共通面と両端を照合する。
規約：同じ span 上の余錐の間の比較。使われ方：β3 の coslice 辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 上下の比較三単体は span の join の共通面で一致する。 -/
lemma dgModuleFiberCofiberComparisonCells_compatible (f : M ⟶ N) :
    SSet.stdSimplex.δ (1 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonLower A D f) :
          (Δ[3] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) =
      SSet.stdSimplex.δ (1 : Fin 4) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonUpper A D f) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparison_common A D f)

/-- Span の join 上の実際の比較写像。 -/
def dgModuleFiberCofiberComparisonJoin (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).desc
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonLower A D f))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonUpper A D f))
    (dgModuleFiberCofiberComparisonCells_compatible A D f)

/-- 左セルへの制限は下側比較三単体。 -/
lemma dgModuleFiberCofiberComparisonJoin_left (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft 1 ≫ dgModuleFiberCofiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonLower A D f) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).inl_desc _ _ _

/-- 右セルへの制限は上側比較三単体。 -/
lemma dgModuleFiberCofiberComparisonJoin_right (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight 1 ≫ dgModuleFiberCofiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonUpper A D f) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 1).inr_desc _ _ _

/-- 比較写像の始点は標準 cofiber 余錐。 -/
lemma dgModuleFiberCofiberComparisonJoin_face_one (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      dgModuleFiberCofiberComparisonJoin A D f =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, Category.assoc,
      dgModuleFiberCofiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonLower_face_three]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, Category.assoc,
      dgModuleFiberCofiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonUpper_face_three]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_upper]

/-- 比較写像の終点は元の標準 fiber 四角形の余錐。 -/
lemma dgModuleFiberCofiberComparisonJoin_face_zero (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      dgModuleFiberCofiberComparisonJoin A D f =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, Category.assoc,
      dgModuleFiberCofiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonLower A D f).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonLower_face_two]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, Category.assoc,
      dgModuleFiberCofiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonUpper_face_two]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_upper]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

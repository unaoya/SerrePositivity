module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleCofiberFiberComparisonTriangles
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanJoinCells
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberBoundaryTriangles

/-! # 比較三単体の join への貼合せ

概要：上下の比較三単体を貼り、標準 cofiber 錐と標準 fiber 錐を結ぶ写像を作る。
方針：cospan の join の二セル表示と、各三単体の零面・一面を使う。
規約：二つの錐は同じ cospan を持つ。使われ方：β3 の実際の slice 比較辺。
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

/-- 上下の比較三単体を貼るための共通面の一致。 -/
lemma dgModuleCofiberFiberComparisonCells_compatible (f : M ⟶ N) :
    SSet.stdSimplex.δ (2 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonLower A D f) :
          (Δ[3] : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) =
      SSet.stdSimplex.δ (2 : Fin 4) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonUpper A D f) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparison_common A D f)

/-- 二つの錐を結ぶ join 上の実際の単体的写像。 -/
def dgModuleCofiberFiberComparisonJoin (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 1).desc
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonLower A D f))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonUpper A D f))
    (dgModuleCofiberFiberComparisonCells_compatible A D f)

/-- 貼合せ写像の左セルは下側比較三単体。 -/
lemma dgModuleCofiberFiberComparisonJoin_left (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft 1 ≫ dgModuleCofiberFiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonLower A D f) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 1).inl_desc _ _ _

/-- 貼合せ写像の右セルは上側比較三単体。 -/
lemma dgModuleCofiberFiberComparisonJoin_right (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight 1 ≫ dgModuleCofiberFiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonUpper A D f) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 1).inr_desc _ _ _

/-- 比較写像の終点は標準 fiber 錐そのもの。 -/
lemma dgModuleCofiberFiberComparisonJoin_face_zero (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet)) ≫
        dgModuleCofiberFiberComparisonJoin A D f =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D (moduleConeInr A D f)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonLower A D f).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonLower_face_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone_left_triangle A D (moduleConeInr A D f)).symm
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonUpper_face_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone_right_triangle A D (moduleConeInr A D f)).symm

/-- 比較写像の始点は元の標準 cofiber 正方形の錐。 -/
lemma dgModuleCofiberFiberComparisonJoin_face_one (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet)) ≫
        dgModuleCofiberFiberComparisonJoin A D f = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)).val
          := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonLower A D f).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonLower_face_one]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight_face, Category.assoc,
      dgModuleCofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonUpper A D f).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonUpper_face_one]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_upper]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberFiberComparisonTriangles
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanJoinCells
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberBoundaryTriangles

/-! # 比較三単体の join への貼合せ

概要：上下の比較三単体を貼り、標準 cofiber 錐と標準 fiber 錐を結ぶ写像を作る。
方針：cospan の join の二セル表示と、各三単体の零面・一面を使う。
規約：二つの錐は同じ cospan を持つ。使われ方：D7 の実際の slice 比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 上下の比較三単体を貼るための共通面の一致。 -/
lemma cofiberFiberComparisonCells_compatible (f : A ⟶ B) (g : A ⟶ C) :
    SSet.stdSimplex.δ (2 : Fin 4) ≫
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonLower f g) :
          (Δ[3] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (2 : Fin 4) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonUpper f g) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparison_common f g)

/-- 二つの錐を結ぶ join 上の実際の単体的写像。 -/
def cofiberFiberComparisonJoin (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 1).desc
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonLower f g))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonUpper f g))
    (cofiberFiberComparisonCells_compatible f g)

/-- 貼合せ写像の左セルは下側比較三単体。 -/
lemma cofiberFiberComparisonJoin_left (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft 1 ≫ cofiberFiberComparisonJoin f g =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonLower f g) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 1).inl_desc _ _ _

/-- 貼合せ写像の右セルは上側比較三単体。 -/
lemma cofiberFiberComparisonJoin_right (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight 1 ≫ cofiberFiberComparisonJoin f g =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonUpper f g) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 1).inr_desc _ _ _

/-- 比較写像の終点は標準 fiber 錐そのもの。 -/
lemma cofiberFiberComparisonJoin_face_zero (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫
        cofiberFiberComparisonJoin f g =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft_face, Category.assoc,
      cofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonLower f g).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonLower_face_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_left_triangle _ _).symm
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight_face, Category.assoc,
      cofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonUpper f g).pullback
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonUpper_face_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_right_triangle _ _).symm

/-- 比較写像の始点は元の標準 cofiber 正方形の錐。 -/
lemma cofiberFiberComparisonJoin_face_one (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫
        cofiberFiberComparisonJoin f g = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoin_isPushout 0).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft_face, Category.assoc,
      cofiberFiberComparisonJoin_left, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonLower f g).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonLower_face_one]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare_lower]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight_face, Category.assoc,
      cofiberFiberComparisonJoin_right, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    change (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonUpper f g).pullback
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom) :
      (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonUpper_face_one]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare_upper]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

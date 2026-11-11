module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberFiberComparisonJoin
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.RebaseCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-! # 標準 cofiber 錐から標準 fiber 錐への実際の辺

概要：貼り合わせた join 写像を curry し、同じ cospan 上の slice の比較辺を作る。
方針：二つの四角形の cospan を同定し、join の端点の等式から始点と終点を確認する。
規約：普遍性による選択に依存しない。使われ方：D7 の極限性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

/-- Curry した比較写像の端点は、join の端点への制限で定まる。 -/
lemma sliceOverCurry_vertex_of_join {K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[1] K ≫ F = p)
    (i : Fin 2) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ i) (𝟙 K) ≫ F = c.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ i (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF)) = c := by
  have hm : SSet.stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF = SSet.yonedaEquiv.symm c := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry_precomp]
    let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ i) (𝟙 K) ≫ F, by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, hF]⟩
    have hd : d = c := Subtype.ext hc
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverCurry_yoneda 0 d).trans (congrArg SSet.yonedaEquiv.symm hd)
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hm]
  exact (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)).apply_symm_apply c

variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 二つの標準四角形は同じ cospan を持つ。 -/
lemma cofiberFiberComparison_cospan (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g) := by
  apply SSet.horn₂₂.isPushout.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare_right]
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_top, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare_top]

/-- 元の cofiber 錐を標準 fiber の cospan 上で読む。 -/
def cofiberFiberSourceCone (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone (cofiberFiberComparison_cospan f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g))

/-- 比較 join 写像は cospan を固定する。 -/
lemma cofiberFiberComparisonJoin_fixed (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonJoin f g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)) := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (SSet.horn 2 2) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1}))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonJoin f g := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonJoin_face_zero]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone _ _).property

/-- 元の錐から標準 fiber 錐への、明示的な slice 比較辺。 -/
def cofiberFiberComparisonSliceEdge (f : A ⟶ B) (g : A ⟶ C) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)))))
      (cofiberFiberSourceCone f g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)) where
  edge := SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonJoin f g) (cofiberFiberComparisonJoin_fixed f g))
  src_eq := sliceOverCurry_vertex_of_join _ _ 1 _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonJoin_face_one f g)
  tgt_eq := sliceOverCurry_vertex_of_join _ _ 0 _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonJoin_face_zero f g)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

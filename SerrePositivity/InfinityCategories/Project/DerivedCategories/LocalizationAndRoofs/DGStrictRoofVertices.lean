module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGStrictRoofNerveMap

/-! # 元の厳密閉分母・閉分子の実屋根頂点

概要：指定閉分母と閉分子から実屋根の零単体を作り、両射影を元の指定頂点へ照合する。
方針：厳密屋根 nerve の指定零単体を写し、全空間写像の二射影の式を評価する。
規約：元の射や対象を選び直さない。使われ方：実細分辺の両端の指定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 指定された元の閉実分母と閉分子を持つ実屋根の頂点。 -/
def dgStrictRoofVertex (P : Set D) (x y : D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : s.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNerveMap A D P x y).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofMk A D P x y s f))

/-- 指定厳密屋根の実分母射影は、元の指定閉分母の頂点。 -/
lemma dgStrictRoofVertex_projection (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : s.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋0⦌)
      (dgStrictRoofVertex A D P x y s f) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s := by
  have h := congrArg (fun F => F.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofMk A D P x y s f))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNerveMap_projection A D P x y)
  refine h.trans ?_
  exact (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋0⦌) z)
    (nerveMap_app_mk₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofDenominator A D P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofMk A D P x y s f))).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_vertex A D P x s)

/-- 指定厳密屋根の実分子射影は、元の指定閉分子の slice 頂点。 -/
lemma dgStrictRoofVertex_target (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : s.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋0⦌)
      (dgStrictRoofVertex A D P x y s f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D f := by
  have h := congrArg (fun F => F.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofMk A D P x y s f))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNerveMap_target A D P x y)
  refine h.trans ?_
  exact (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D y).app (Opposite.op ⦋0⦌) z)
    (nerveMap_app_mk₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofNumerator A D P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofMk A D P x y s f))).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap_vertex A D y (Over.mk f))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
